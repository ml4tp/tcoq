open Names
open Term
open Pp
open Printer
open Vernacexpr

open Locus
open Tacexpr
open Genredexpr
open Misctypes
open Glob_term
open Globnames
open Constrexpr
open Genarg
open Impargs

open CErrors


(* [Note] 
 *
 * Contains functionality for ML4TP. Prints out the tactic state of a Coq proof.
 * We output a "shared" representation of a Coq tactic state.
 *   1. Low-level format of expressions uses sharing
 *   2. Low-level format of tactic states outputs identifiers, types as shared
 *      expressions, and shared goal
 * 
 * We may have been able to use Coq-SerAPI, but I don't think it handles
 *   1. Outputting of shared representation
 *   2. Breaking up of semicolons
 *
 * I have no idea why using a hashtable doesn't speed up compared to hashmap version.
 * I commented out the hashtable version.
 *)


module IntSet = Set.Make(struct type t = int let compare = compare end)


(* ************************************************************************** *)
(* Output *)

let dump_ch = 
  match Sys.getenv_opt "TCOQ_DUMP" with
  | Some f -> open_out "/tmp/tcoq.log"
  | None -> stdout
let ml4tp_write s = Printf.fprintf dump_ch "%s" s
let ml4tp_flush () = flush dump_ch



(* ************************************************************************** *)
(* Simple fresh id generation *)

module GenSym =
  struct
    type gensym = int ref
    let init () = ref 0
    let reset counter = counter := 0
    let fresh counter =
      let old = !counter in
      counter := (!counter) + 1;
      old
  end

(* External counters *)

let gs_callid = GenSym.init ()
let fresh_callid () = GenSym.fresh gs_callid

let gs1 = GenSym.init ()
let fresh_gs1 () = GenSym.fresh gs1

let gs2 = GenSym.init ()
let fresh_gs2 () = GenSym.fresh gs2

let gs3 = GenSym.init ()
let fresh_gs3 () = GenSym.fresh gs3

let gs4 = GenSym.init ()
let fresh_gs4 () = GenSym.fresh gs4


(* NOTE(deh): does this have any uses? *)
let kludge_env = ref Environ.empty_env
let set_kludge_env env = kludge_env := env



(* ************************************************************************** *)
(* Utility functions *)

(* Showing *)

let show_ls f sep ls =
  String.concat sep (List.map f ls)

let show_arr f sep arr =
  let arr' = Array.map f arr in
  String.concat sep (Array.to_list arr')

let brackets s = Printf.sprintf "[%s]" s
let parens s = Printf.sprintf "(%s)" s

let show_maybe f maybe =
  match maybe with
  | None -> "N"
  | Some x -> Printf.sprintf "(S %s)" (f x)

let gs_anon = GenSym.init ()
let fresh_anon () = GenSym.fresh gs_anon

let show_id = Names.Id.to_string

let show_name name =
  match name with
  | Anonymous ->  let x = fresh_anon () in Printf.sprintf "$A%d" x
  | Name id -> show_id id

let show_gname (loc, id) = show_id id

let show_evar ev =
  Evar.repr ev

let show_or_var f ov =
  match ov with
  | ArgArg x -> Printf.sprintf "(A %s)" (f x )
  | ArgVar (loc, id) -> Printf.sprintf "(V %s)" (show_id id)


(* Other *)

let replace input output =
  Str.global_replace (Str.regexp_string input) output

let pp2str pp =
  replace "\n" " " (string_of_ppcmds (h 0 pp))



(* ************************************************************************** *)
(* Create shared Coq expressions *)

let gs_constridx = GenSym.init ()
let fresh_constridx () = GenSym.fresh gs_constridx

module ConstrHash =
  struct
    type t = Term.constr
    let equal c1 c2 = Term.eq_constr c1 c2
    let hash c = Term.hash_constr c
  end
module ConstrHashtbl = Hashtbl.Make(ConstrHash)


(* Map an expression to an index *)
let constr_shareM = ConstrHashtbl.create 2000
let clear_constr_shareM () = ConstrHashtbl.clear constr_shareM


(* Map an index to its low-level expression *)
module IntMap = Map.Make(struct type t = int let compare = compare end)
module IntTbl = Hashtbl.Make(struct type t = int let equal i j = i = j let hash i = i land max_int end)
let tacst_low_constrM = ref (IntMap.empty)
let clear_tacst_low_constrM () = tacst_low_constrM := IntMap.empty
let dump_low_constrM () = 
  IntMap.iter (fun k v -> ml4tp_write (Printf.sprintf "%d: %s\n" k v)) !tacst_low_constrM

(* NOTE(deh): switch for hashtable *)
(*
let tacst_low_constrM = IntTbl.create 4000
let clear_tacst_low_constrM () = IntTbl.clear tacst_low_constrM
let dump_low_constrM () = 
  IntTbl.iter (fun k v -> ml4tp_write (Printf.sprintf "%d: %s\n" k v)) tacst_low_constrM
*)

(* Keep track of new-bindings added *)
let new_low_constrs = ref []
let clear_new_low_constrs () = new_low_constrs := []
let add_new_low_constrs v = new_low_constrs := v :: !new_low_constrs

let with_constr_idx constr value =
  let idx = fresh_constridx () in
  ConstrHashtbl.add (constr_shareM) constr idx;
  tacst_low_constrM := IntMap.add idx value !tacst_low_constrM;
  (* NOTE(deh): switch for hashtable *)
  (* IntTbl.add tacst_low_constrM idx value; *)
  add_new_low_constrs (idx, value);
  idx

let rec share_constr constr =
  match ConstrHashtbl.find_opt (constr_shareM) constr with
  | Some idx -> idx
  | None -> 
      match kind_of_term constr with
      | Rel i -> with_constr_idx constr (Printf.sprintf "R %d" i)
      | Var id -> with_constr_idx constr (Printf.sprintf "V %s" (string_of_id id))
      | Meta mv -> with_constr_idx constr (Printf.sprintf "M %d" mv)
      | Evar (exk, cs) -> 
          let idxs = (share_constrs cs) in
          with_constr_idx constr (Printf.sprintf "E %d [%s]" (show_evar exk) idxs)
      | Sort sort -> with_constr_idx constr (Printf.sprintf "S %s" (string_of_ppcmds (Univ.Universe.pr (Sorts.univ_of_sort sort))))
      | Cast (c, ck, t) ->
          let idx1 = share_constr c in
          let idx2 = share_constr t in
           with_constr_idx constr (Printf.sprintf "CA %d %s %d" idx1 (share_cast_kind ck) idx2)
      | Prod (name, t1, t2) ->
          let idx1 = share_constr t1 in
          let idx2 = share_constr t2 in
          with_constr_idx constr (Printf.sprintf "P %s %d %d" (show_name name) idx1 idx2)
      | Lambda (name, t, c) -> 
          let idx1 = (share_constr t) in
          let idx2 = (share_constr c) in 
          with_constr_idx constr (Printf.sprintf "L %s %d %d" (show_name name) idx1 idx2)
      | LetIn (name, c1, t, c2) ->
          let idx1 = (share_constr c1) in
          let idx2 = (share_constr t) in  
          let idx3 = (share_constr c2) in  
          with_constr_idx constr (Printf.sprintf "LI %s %d %d %d" (show_name name) idx1 idx2 idx3)
      | App (c, cs) -> 
          let idx1 = (share_constr c) in
          let idxs = (share_constrs cs) in
          with_constr_idx constr (Printf.sprintf "A %d [%s]" idx1 idxs)
      | Const (const, ui) -> 
          with_constr_idx constr (Printf.sprintf "C %s [%s]" (Names.Constant.to_string const) (share_universe_instance ui))
      | Ind (ind, ui) ->
          let (mutind, pos) = share_inductive ind in
          with_constr_idx constr (Printf.sprintf "I %s %d [%s]" mutind pos (share_universe_instance ui))
      | Construct ((ind, conid), ui) ->
          let (mutind, pos) = share_inductive ind in
          with_constr_idx constr (Printf.sprintf "CO %s %d %d [%s]" mutind pos conid (share_universe_instance ui))
      | Case (ci, c1, c2, cs) ->
          let idx1 = share_constr c1 in
          let idx2 = share_constr c2 in
          let idxs = share_constrs cs in
          with_constr_idx constr (Printf.sprintf "CS [%s] %d %d [%s]" (share_case_info ci) idx1 idx2 idxs)
      | Fix ((iarr, i), pc) ->
          let (ns, ts, cs) = share_prec_declaration pc in
          with_constr_idx constr (Printf.sprintf "F [%s] %d [%s] [%s] [%s]" (share_int_arr iarr) i ns ts cs)
      | CoFix (i, pc) -> 
          let (ns, ts, cs) = share_prec_declaration pc in
          with_constr_idx constr (Printf.sprintf "CF %d [%s] [%s] [%s]" i ns ts cs)
      | Proj (proj, c) -> 
          let idx1 = share_constr c in
          with_constr_idx constr (Printf.sprintf "PJ %s %d" (Names.Projection.to_string proj) idx1)
and share_constrs cs =
  show_arr (fun c -> string_of_int (share_constr c)) " " cs
and share_cast_kind ck =
  match ck with
  | VMcast -> "V"
  | NATIVEcast -> "N"
  | DEFAULTcast -> "D"
  | REVERTcast -> "R"
and share_universe_instance ui =
  show_arr Univ.Level.to_string " " (Univ.Instance.to_array ui)
and share_inductive (mutind, pos) =
  (Names.MutInd.to_string mutind, pos)
and share_prec_declaration (names, types, constrs) =
  let names' = show_arr show_name " " names in
  let types' = share_constrs types in
  let constrs' = share_constrs constrs in
  (names', types', constrs')
and share_int_arr iarr =
  show_arr string_of_int " " iarr
and share_case_info ci =
  let (mutind, pos) = share_inductive ci.ci_ind in
  Printf.sprintf "%s %d %d [%s] [%s]" mutind pos (ci.ci_npar) (share_int_arr ci.ci_cstr_ndecls) (share_int_arr ci.ci_cstr_nargs)

let show_constr c = string_of_int (share_constr c)



(* ************************************************************************** *)
(* Glob_constr printing *)

(* Note(deh): 
 *
 * We need this layer because Coq tactics use constr_expr/glob_constr.
 *
 * 1. [constr_expr] is what the user writes
 * 2. [glob_constr] is desugared, but without types (i.e., no inference).
 * 3. [constr] is Coq kernel representation of Gallina terms
 *
 *)

let show_sexpr_ls show ls =
  parens (show_ls show " " ls)

let show_sexpr_arr show arr =
  parens (show_arr show " " arr)

let rec show_global_reference gr =
  match gr with
  | VarRef v ->
      Printf.sprintf "(VR %s)" (show_id v)
  | ConstRef v ->
      Printf.sprintf "(CR %s)" (Names.Constant.to_string v)
  | IndRef (mi, i) ->
      Printf.sprintf "(IR %s %d)" (Names.MutInd.to_string mi) i
  | ConstructRef ((mi, i), j) ->
      Printf.sprintf "(TR %s %d %d)" (Names.MutInd.to_string mi) i j

let show_cast_type show ct = 
  match ct with
  | CastConv a -> Printf.sprintf "(C %s)" (show a)
  | CastVM a -> Printf.sprintf "(VM %s)" (show a)
  | CastCoerce -> Printf.sprintf "O"
  | CastNative a -> Printf.sprintf "(N %s)" (show a)

let show_sort_info si =
  show_sexpr_ls (fun (loc, s) -> s) si

let show_glob_sort gs =
  match gs with
  | GProp -> "P"
  | GSet -> "S"
  | GType si -> Printf.sprintf "(T %s)" (show_sort_info si) 


let rec show_intro_pattern_expr show ipe =
  match ipe with
  | IntroForthcoming b ->
      Printf.sprintf "(F %b)" b
  | IntroNaming ipne ->
      Printf.sprintf "(N %s)" (show_intro_pattern_naming_expr ipne)
  | IntroAction ipae ->
      Printf.sprintf "(A %s)" (show_intro_pattern_action_expr show ipae)
and show_intro_pattern_naming_expr ipne =
  match ipne with
  | IntroIdentifier id ->
      Printf.sprintf "(I %s)" (show_id id)
  | IntroFresh id ->
      Printf.sprintf "(F %s)" (show_id id)
  | IntroAnonymous ->
      "A"
and show_intro_pattern_action_expr show ipae =
  match ipae with
  | IntroWildcard ->
      "W"
  | IntroOrAndPattern oaipe ->
      Printf.sprintf "(O %s)" (show_or_and_intro_pattern_expr show oaipe)
  | IntroInjection ls ->
      Printf.sprintf "(I %s)" (show_sexpr_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ls)
  | IntroApplyOn (a, (loc, ipe)) ->
      Printf.sprintf "(A %s %s)" (show a) (show_intro_pattern_expr show ipe)
  | IntroRewrite b ->
      Printf.sprintf "(R %b)" b
and show_or_and_intro_pattern_expr show oaipe = 
  match oaipe with
  | IntroOrPattern ls ->
      Printf.sprintf "(I %s)" (show_sexpr_ls (fun ls' -> show_sexpr_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ls') ls)
  | IntroAndPattern ls ->
      Printf.sprintf "(A %s)" (show_sexpr_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ls)

let rec show_cases_pattern cp =
  match cp with
  | PatVar (loc, n) ->
      Printf.sprintf "(V %s)" (show_name n)
  | PatCstr (loc, ((mutind, i), j), cps, n) ->
      Printf.sprintf "(C %s %d %d %s %s)" (Names.MutInd.to_string mutind) i j (show_sexpr_ls show_cases_pattern cps) (show_name n)


(* ======================================== *)

let genarg_showrule = ref Util.String.Map.empty

let declare_extra_genarg_showrule wit f g h =
  let s = match wit with
    | ExtraArg s -> ArgT.repr s
    | _ -> error
      "Can declare a pretty-printing rule only for extra argument types."
  in
  let f x = f (out_gen (rawwit wit) x) in
  let g x = g (out_gen (glbwit wit) x) in
  let h x = h (out_gen (topwit wit) x) in
  genarg_showrule := Util.String.Map.add s (f, g, h) !genarg_showrule

let declare_extra_genarg_showrule1 wit g =
  declare_extra_genarg_showrule wit (fun _ -> "") g (fun _ -> "")

let add_genarg tag show =
  let wit = Genarg.make0 tag in
  let tag = Geninterp.Val.create tag in
  let glob ist x = (ist, x) in
  let subst _ x = x in
  let interp ist x = Ftactic.return (Geninterp.Val.Dyn (tag, x)) in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit interp in
  let () = Geninterp.register_val0 wit (Some (Geninterp.Val.Base tag)) in
  declare_extra_genarg_showrule wit show show show;
  wit

let _ = 
  add_genarg "FOO" (fun () -> "FOO")

(* ======================================== *)


let rec show_generic_arg ga =
  match ga with
  | GenArg (Glbwit wit, x) ->
    match wit with
    | ListArg wit -> 
        Printf.sprintf "(L %s)" (show_sexpr_ls (fun y -> show_generic_arg (in_gen (glbwit wit) y)) x)
    | OptArg wit ->
        Printf.sprintf "(O %s)" (show_maybe (fun y -> show_generic_arg (in_gen (glbwit wit) y)) x)
    | PairArg (wit1, wit2) ->
        let p, q = x in
        let p = in_gen (glbwit wit1) p in
        let q = in_gen (glbwit wit2) q in
        Printf.sprintf "(P %s %s)" (show_generic_arg p) (show_generic_arg q)
    | ExtraArg s ->
        try
          let y = Util.pi2 (Util.String.Map.find (ArgT.repr s) !genarg_showrule) (in_gen (glbwit wit) x) in
          Printf.sprintf "(E %s %s)" (ArgT.repr s) y
        with Not_found -> ArgT.repr s


let rec show_ltac_constant lc =
  Names.KerName.to_string lc
and show_g_reference gref =
  show_or_var (fun (loc, lc) -> show_ltac_constant lc) gref


let show_evar_kinds = function
  | Evar_kinds.ImplicitArg (gref, (i, m_id), b) ->
      Printf.sprintf "(A %s %d %s %b)" (show_global_reference gref) i (show_maybe show_id m_id) b
  | Evar_kinds.BinderType name ->
      Printf.sprintf "(B %s)" (show_name name)
  | Evar_kinds.QuestionMark ods ->
      let f ods =
        match ods with
        | Evar_kinds.Define b -> Printf.sprintf "(D %b)" b
        | Evar_kinds.Expand -> "E"
      in
      Printf.sprintf "(Q %s)" (f ods)
  | Evar_kinds.CasesType b ->
      Printf.sprintf "(C %b)" b
  | Evar_kinds.InternalHole ->
      "H"
  | Evar_kinds.TomatchTypeParameter ((mutind, i), j) ->
      Printf.sprintf "(T %s %d %d)" (Names.MutInd.to_string mutind) i j
  | Evar_kinds.GoalEvar ->
      "G"
  | Evar_kinds.ImpossibleCase ->
      "I"
  | Evar_kinds.MatchingVar (b, id) ->
      Printf.sprintf "(M %b %s)" b (show_id id)
  | Evar_kinds.VarInstance id ->
      Printf.sprintf "(V %s)" (show_id id)
  | Evar_kinds.SubEvar ek ->
      Printf.sprintf "(E %d)" (show_evar ek)


let show_case_style csty =
  match csty with
  | LetStyle -> "L"
  | IfStyle -> "I"
  | LetPatternStyle -> "LP"
  | MatchStyle -> "M"
  | RegularStyle -> "R"


let show_binding_kind bk =
  match bk with
  | Decl_kinds.Explicit -> "E"
  | Decl_kinds.Implicit -> "I"


let show_predicate_pattern (n, m_args) =
  let f (loc, (mutind, i), ns) = Printf.sprintf "(%s %d %s)" (Names.MutInd.to_string mutind) i (show_sexpr_ls show_name ns) in
  Printf.sprintf "(%s %s)" (show_name n) (show_maybe f m_args)
let show_tomatch_tuple show_gc (gc, pp) =
  Printf.sprintf "(%s %s)" (show_gc gc) (show_predicate_pattern pp)
let show_tomatch_tuples show_gc tmts =
  show_sexpr_ls (show_tomatch_tuple show_gc) tmts


let show_case_clause show_gc (loc, ids, cps, gc) = 
  Printf.sprintf "(%s %s %s)" (show_sexpr_ls show_id ids) (show_sexpr_ls show_cases_pattern cps) (show_gc gc)
let show_case_clauses show_gc ccs =
  show_sexpr_ls (show_case_clause show_gc) ccs


let show_fix_recursion_order show_gc fro =
  match fro with
  | GStructRec ->
      "S"
  | GWfRec gc ->
      Printf.sprintf "(W %s)" (show_gc gc)
  | GMeasureRec (gc, m_gc) ->
      Printf.sprintf "(M %s %s)" (show_gc gc) (show_maybe show_gc m_gc)
let show_fix_kind show_gc fk =
  match fk with
  | GFix (ifros, i) ->
      let f (m_j, fro) = Printf.sprintf "(%s %s)" (show_maybe string_of_int m_j) (show_fix_recursion_order show_gc fro) in
      Printf.sprintf "(F %s %d)" (show_sexpr_arr f ifros) i
  | GCoFix i ->
      Printf.sprintf "(C %d)" i
let show_glob_decl show_gc (name, bk, m_c, c) =
  Printf.sprintf "(%s %s %s %s)" (show_name name) (show_binding_kind bk) (show_maybe show_gc m_c) (show_gc c)


let show_argument_position ap =
  match ap with
  | Conclusion -> "C"
  | Hyp i -> Printf.sprintf "(H %d)" i


let show_implicit_explanation ie =
  match ie with
  | DepRigid ap ->
      Printf.sprintf "(R %s)" (show_argument_position ap)
  | DepFlex ap ->
      Printf.sprintf "(F %s)" (show_argument_position ap)
  | DepFlexAndRigid (ap1, ap2) ->
      Printf.sprintf "(B %s %s)" (show_argument_position ap1) (show_argument_position ap2)
  | Manual ->
      "M"

let rec show_glob_constr gc =
  match gc with
  | GRef (l, gr, _) ->
      Printf.sprintf "(! %s)" (show_global_reference gr)
  | GVar (l, id) ->
      Printf.sprintf "(V %s)" (show_id id)
  | GEvar (l, en, args) -> 
      let f (id, gc) = Printf.sprintf "(%s %s)" (show_id id) (show_glob_constr gc) in
      Printf.sprintf "(E %s %s)" (show_id en) (show_sexpr_ls f args)
  | GPatVar (l, (b, pv)) ->
      Printf.sprintf "(PV %b %s)" b (show_id pv)
  | GApp (l, gc, gcs) ->
      begin match gc with
      | GRef (l, gr, _) ->
          let imps = implicits_of_global gr in
          let f (id, ie, (mi, fi)) = Printf.sprintf "(%s %s)" (show_id id) (show_implicit_explanation ie) in
          Printf.sprintf "(A %s %s %s)" (show_glob_constr gc) (show_glob_constrs gcs) (show_sexpr_ls (show_sexpr_ls (show_maybe f)) (List.map snd imps))
      | _ ->
          Printf.sprintf "(A %s %s ())" (show_glob_constr gc) (show_glob_constrs gcs)
      end
  | GLambda (l, n, bk, gc1, gc2) ->
      Printf.sprintf "(L %s %s %s %s)" (show_name n) (show_binding_kind bk) (show_glob_constr gc1) (show_glob_constr gc2)
  | GProd (l, n, bk, gc1, gc2) ->
      Printf.sprintf "(P %s %s %s %s)" (show_name n) (show_binding_kind bk) (show_glob_constr gc1) (show_glob_constr gc2)
  | GLetIn (l, n, gc1, gc2) ->
      Printf.sprintf "(LI %s %s %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
  | GCases (l, csty, m_gc, tups, ccs) ->
      Printf.sprintf "(C %s %s %s %s)" (show_case_style csty) (show_maybe show_glob_constr m_gc) (show_tomatch_tuples show_glob_constr tups) (show_case_clauses show_glob_constr ccs)
  | GLetTuple (l, ns, arg, gc1, gc2) ->
      let f (name, m_gc) = Printf.sprintf "(%s %s)" (show_name name) (show_maybe show_glob_constr m_gc) in
      Printf.sprintf "(LT %s %s %s %s)" (show_sexpr_ls show_name ns) (f arg) (show_glob_constr gc1) (show_glob_constr gc2)
  | GIf (l, gc, (n, m_gc), gc2, gc3) ->
      let s = Printf.sprintf "(%s %s)" (show_name n) (show_maybe show_glob_constr m_gc) in
      Printf.sprintf "(I %s %s %s %s)" (show_glob_constr gc) s (show_glob_constr gc2) (show_glob_constr gc3)
  | GRec (l, fk, ids, gdss, gcs1, gcs2) ->
      Printf.sprintf "(R %s %s %s %s %s)" (show_fix_kind show_glob_constr fk) (show_sexpr_arr show_id ids) (show_sexpr_arr (show_sexpr_ls (show_glob_decl show_glob_constr)) gdss) (show_glob_constr_arr gcs1) (show_glob_constr_arr gcs2)
  | GSort (l, gsort) ->
      Printf.sprintf "(S %s)" (show_glob_sort gsort)
  | GHole (l, k, ipne, m_gga) ->
      Printf.sprintf "(H %s %s %s)" (show_evar_kinds k) (show_intro_pattern_naming_expr ipne) (show_maybe show_generic_arg m_gga)
  | GCast (l, gc, gc_ty) ->
      Printf.sprintf "(T %s %s)" (show_glob_constr gc) (show_cast_type show_glob_constr gc_ty)
and show_glob_constrs gcs =
  show_sexpr_ls show_glob_constr gcs
and show_glob_constr_arr gcs =
  show_sexpr_arr show_glob_constr gcs



(* ************************************************************************** *)
(* Glob_constr equality/hashing *)

let eq_maybe eq = function
  | None, None -> true
  | Some x, Some x' -> eq x x'
  | _, _ -> false


let eq_ls eq ls ls' =
  if List.length ls = List.length ls'
  then List.fold_left (fun acc (x, x') -> eq x x' && acc) true (List.combine ls ls')
  else false


let eq_arr eq arr arr' =
  if Array.length arr = Array.length arr'
  then Array.for_all (fun x -> x) (Array.map2 (fun x x' -> eq x x') arr arr')
  else false


let eq_global_reference gr gr' =
  match gr, gr' with
  | VarRef v, VarRef v' ->
      Id.equal v v'
  | ConstRef c, ConstRef c' ->
      eq_constant c c'
  | IndRef c, IndRef c' ->
      eq_ind c c'
  | ConstructRef c, ConstructRef c' ->
      eq_constructor c c'
  | _, _ -> false


let eq_case_style csty csty' =
  match csty, csty' with
  | LetStyle, LetStyle -> true
  | IfStyle, IfStyle -> true
  | LetPatternStyle, LetPatternStyle -> true
  | MatchStyle, MatchStyle -> true
  | RegularStyle, RegularStyle -> true
  | _, _ -> false


let rec eq_gc gc1 gc2 =
  match gc1, gc2 with
  | GRef (_, gr, _), GRef (_, gr', _) -> 
      eq_global_reference gr gr'
  | GVar (_, id), GVar (_, id') ->
      Id.equal id id'
  | GEvar (_, en, args), GEvar (_, en', args') ->
      Id.equal en en' && eq_ls (fun (n, gc) (n', gc') -> Id.equal n n' && eq_gc gc gc') args args'
  | GPatVar (_, (b, pv)), GPatVar (_, (b', pv')) ->
      b = b' && Id.equal pv pv'
  | GApp (_, gc, gcs), GApp (_, gc', gcs') ->
      eq_gc gc gc' && eq_gc_ls gcs gcs'
  | GLambda (_, n, bk, gc1, gc2), GLambda (_, n', bk', gc1', gc2') ->
      eq_gc gc1 gc1' && eq_gc gc2 gc2'
  | GProd (_, n, bk, gc1, gc2), GProd (_, n', bk', gc1', gc2') ->
      eq_gc gc1 gc1' && eq_gc gc2 gc2'
  | GLetIn (_, n, gc1, gc2), GLetIn (_, n', gc1', gc2') ->
      eq_gc gc1 gc1' && eq_gc gc2 gc2'
  | GCases (_, csty, m_gc, tups, ccs), GCases (_, csty', m_gc', tups', ccs') ->
      eq_case_style csty csty' && eq_maybe eq_gc (m_gc, m_gc') && eq_tomatch_tuples tups tups' && eq_case_clauses ccs ccs'
  | GLetTuple (_, ns, (n, m_gc), gc1, gc2), GLetTuple (_, ns', (n', m_gc'), gc1', gc2') ->
      eq_maybe eq_gc (m_gc, m_gc') && eq_gc gc1 gc1' && eq_gc gc2 gc2'
  | GIf (_, gc, (n, m_gc), gc2, gc3), GIf (_, gc', (n', m_gc'), gc2', gc3') ->
      eq_gc gc gc' && eq_maybe eq_gc (m_gc, m_gc') && eq_gc gc2 gc2' && eq_gc gc3 gc3'
  | GRec (_, fk, ids, gdss, gcs1, gcs2), GRec (_, fk', ids', gdss', gcs1', gcs2') ->
     eq_fix_kind fk fk' && eq_arr Id.equal ids ids' && eq_arr (eq_ls eq_glob_decl) gdss gdss' && eq_gc_arr gcs1 gcs1' && eq_gc_arr gcs2 gcs2'
  | GSort (_, gsort), GSort (_, gsort') ->
      (* Being lazy ... convert to string and check *)
      String.equal (show_glob_constr gc1) (show_glob_constr gc2)
  | GHole (_, k, ipne, m_gga), GHole (_, k', ipne', m_gga') ->
      (* Being lazy ... convert to string and check *)
      String.equal (show_glob_constr gc1) (show_glob_constr gc2)
  | GCast (_, gc, gc_ty), GCast (_, gc', gc_ty') ->
      eq_gc gc gc' && eq_cast_type gc_ty gc_ty'
  | _, _ -> false

and eq_gc_ls gcs gcs' =
  eq_ls eq_gc gcs gcs'
and eq_gc_arr gcs gcs' =
  eq_arr eq_gc gcs gcs'
  (* Array.for_all (fun x -> x) (Array.map2 (fun gc gc' -> eq_gc gc gc') gcs gcs') *)

and eq_cast_type ct ct' = 
  match ct, ct' with
  | CastConv a, CastConv a' -> eq_gc a a'
  | CastVM a, CastVM a' -> eq_gc a a'
  | CastCoerce, CastCoerce -> true
  | CastNative a, CastNative a' -> eq_gc a a'
  | _, _ -> false

and eq_predicate_pattern (n, m_args) (n', m_args') =
  Name.equal n n' && eq_maybe (fun (_, ind, ns) (_, ind', ns') -> eq_ind ind ind') (m_args, m_args')
and eq_tomatch_tuple (gc, pp) (gc', pp') =
  eq_gc gc gc' && eq_predicate_pattern pp pp'
and eq_tomatch_tuples tmts tmts' =
  eq_ls eq_tomatch_tuple tmts tmts'

and eq_cases_pattern cp cp' =
  match cp, cp' with
  | PatVar (_, n), PatVar (_, n') ->
      Name.equal n n'
  | PatCstr (_, c, cps, n), PatCstr (_, c', cps', n') ->
      eq_constructor c c' && eq_ls (fun cp cp' -> eq_cases_pattern cp cp') cps cps' && Name.equal n n'
  | _, _ -> false
and eq_case_clause (loc, ids, cps, gc) (loc', ids', cps', gc') =
  eq_gc gc gc' && eq_ls eq_cases_pattern cps cps'
and eq_case_clauses ccs ccs' =
  eq_ls (fun cc cc' -> eq_case_clause cc cc') ccs ccs'

and eq_fix_recursion_order fro fro' =
  match fro, fro' with
  | GStructRec, GStructRec ->
      true
  | GWfRec gc, GWfRec gc' ->
      eq_gc gc gc'
  | GMeasureRec (gc, m_gc), GMeasureRec (gc', m_gc') ->
      eq_gc gc gc' && eq_maybe eq_gc (m_gc, m_gc')
  | _, _ -> 
      false
and eq_fix_kind fk fk' =
  match fk, fk' with
  | GFix (ifros, i), GFix (ifros', i') ->
      i = i' && eq_arr (fun (m_j, fro) (m_j', fro') -> eq_maybe (=) (m_j, m_j') && eq_fix_recursion_order fro fro') ifros ifros'
  | GCoFix i, GCoFix i' ->
      i = i'
  | _, _ -> 
      false
and eq_glob_decl (name, bk, m_c, c) (name', bk', m_c', c') =
  eq_maybe eq_gc (m_c, m_c') && eq_gc c c'


open Hashset.Combine


let hash_global_reference gr =
  match gr with
  | VarRef v ->
      combinesmall 1 (Id.hash v)
  | ConstRef v ->
      combinesmall 2 (Constant.hash v)
  | IndRef ind ->
      combinesmall 3 (ind_hash ind)
  | ConstructRef c ->
      combinesmall 4 (constructor_hash c)


let hash_glob_sort gsort =
  match gsort with
  | GProp ->
      combinesmall 16 0
  | GSet ->
      combinesmall 16 1
  | GType si ->
      combinesmall 16 2


let hash_intro_pattern_naming_expr ipne =
  match ipne with
  | IntroIdentifier id ->
      combine 0 (Id.hash id)
  | IntroFresh id ->
      combine 1 (Id.hash id)
  | IntroAnonymous ->
      2


let hash_evar_kinds = function
  | Evar_kinds.ImplicitArg (gr, (i, m_id), b) ->
      combinesmall 1 (hash_global_reference gr)
  | Evar_kinds.BinderType name ->
      2
  | Evar_kinds.QuestionMark ods -> begin
      match ods with
      | Evar_kinds.Define b -> 3
      | Evar_kinds.Expand -> 4
      end
  | Evar_kinds.CasesType b ->
      5
  | Evar_kinds.InternalHole ->
      6
  | Evar_kinds.TomatchTypeParameter (ind, j) ->
      combinesmall 7 (ind_hash ind)
  | Evar_kinds.GoalEvar ->
      8
  | Evar_kinds.ImpossibleCase ->
      9
  | Evar_kinds.MatchingVar (b, id) ->
      combinesmall 10 (Id.hash id)
  | Evar_kinds.VarInstance id ->
      combinesmall 11 (Id.hash id)
  | Evar_kinds.SubEvar ek ->
      combinesmall 12 (Evar.hash ek)


let rec hash_gc = function
  | GRef (_, gr, _) ->
      hash_global_reference gr
  | GVar (_, id) ->
      combinesmall 5 (Id.hash id)
  | GEvar (_, en, args) ->
      let f (n, gc) = combine (Id.hash n) (hash_gc gc) in
      combinesmall 6 (List.fold_left (fun acc x -> combine (f x) acc) 0 args)
  | GPatVar (_, (b, pv)) ->
      combinesmall 7 (Id.hash pv)
  | GApp (l, gc, gcs) ->
      combinesmall 8 (combine (hash_gc_ls gcs) (hash_gc gc))
  | GLambda (_, n, bk, gc1, gc2) ->
      combinesmall 9 (combine (hash_gc gc1) (hash_gc gc2))
  | GProd (_, n, bk, gc1, gc2) ->
      combinesmall 10 (combine (hash_gc gc1) (hash_gc gc2))
  | GLetIn (_, n, gc1, gc2) ->
      combinesmall 11 (combine (hash_gc gc1) (hash_gc gc2))
  | GCases (_, csty, m_gc, tups, ccs) ->
      combinesmall 12 (hash_case_clauses ccs)
  | GLetTuple (l, ns, arg, gc1, gc2) ->
      combinesmall 13 (combine (hash_gc gc1) (hash_gc gc2))
  | GIf (_, gc, (n, m_gc), gc2, gc3) ->
      combinesmall 14 (combine3 (hash_gc gc) (hash_gc gc2) (hash_gc gc3))
  | GRec (_, fk, ids, gdss, gcs1, gcs2) ->
      combinesmall 15 (combine (hash_gc_arr gcs1) (hash_gc_arr gcs2))
  | GSort (_, gsort) ->
      combinesmall 16 (hash_glob_sort gsort)
  | GHole (_, k, ipne, m_gga) ->
      combinesmall 18 (combine (hash_evar_kinds k) (hash_intro_pattern_naming_expr ipne))
  | GCast (_, gc, gc_ty) ->
      let hc = hash_gc gc in
      let ht = 
        match gc_ty with
        | CastConv a -> combine3 hc 0 (hash_gc a)
        | CastVM a -> combine3 hc 1 (hash_gc a)
        | CastCoerce -> combine hc 2
        | CastNative a -> combine3 hc 3 (hash_gc a)
      in
        combinesmall 19 ht

and hash_gc_ls gcs =
  List.fold_left (fun acc gc -> combine (hash_gc gc) acc) 0 gcs
and hash_gc_arr gcs =
  Array.fold_left (fun acc gc -> combine (hash_gc gc) acc) 0 gcs

and hash_cases_pattern cp =
  match cp with
  | PatVar (_, n) ->
      1
  | PatCstr (_, (ind, j), cps, n) ->
      let hcps = List.fold_left (fun acc cp -> combine (hash_cases_pattern cp) acc) 0 cps in
      combinesmall 2 (combine (ind_hash ind) hcps)
and hash_case_clause (loc, ids, cps, gc) = 
  combine (hash_gc gc) (List.fold_left (fun acc cp -> combine (hash_cases_pattern cp) acc) 0 cps)
and hash_case_clauses ccs =
  List.fold_left (fun acc cc -> combine (hash_case_clause cc) acc) 0 ccs



(* ************************************************************************** *)
(* Create shared glob_constr *)

let gs_gc_idx = GenSym.init ()
let fresh_gc_idx () = GenSym.fresh gs_gc_idx

let eq_gc' gc1 gc2 =
  String.equal (show_glob_constr gc1) (show_glob_constr gc2)

module GlobConstrHash =
  struct
    type t = glob_constr
    let equal c1 c2 = eq_gc c1 c2   (* Note(deh): problem potentially ... *)
    let hash c = hash_gc c
  end
module GlobConstrHashtbl = Hashtbl.Make(GlobConstrHash)


(* Map an expression to an index *)
let gc_shareM = GlobConstrHashtbl.create 2000
let clear_gc_shareM () = GlobConstrHashtbl.clear gc_shareM


(* Map an index to its low-level expression *)
let tacst_low_gcM = ref (IntMap.empty)
let clear_tacst_low_gcM () = tacst_low_gcM := IntMap.empty
let dump_low_gcM () = 
  IntMap.iter (fun k v -> ml4tp_write (Printf.sprintf "%d: %s\n" k v)) !tacst_low_gcM

(* Keep track of new-bindings added *)
let new_low_gcs = ref []
let clear_new_low_gcs () = new_low_gcs := []
let add_new_low_gcs v = new_low_gcs := v :: !new_low_gcs


let with_gc_idx gc value =
  let idx = fresh_gc_idx () in
  GlobConstrHashtbl.add (gc_shareM) gc idx;
  tacst_low_gcM := IntMap.add idx value !tacst_low_gcM;
  add_new_low_gcs (idx, value);
  idx


(* Print out sexprs but with indicies for terms *)
let rec share_glob_constr glob_constr =
  match GlobConstrHashtbl.find_opt (gc_shareM) glob_constr with
  | Some idx -> idx
  | None ->
      match glob_constr with
      | GRef (_, gr, _) ->
          with_gc_idx glob_constr (Printf.sprintf "(! %s)" (show_global_reference gr))
      | GVar (_, id) ->
          with_gc_idx glob_constr (Printf.sprintf "(V %s)" (show_id id))
      | GEvar (_, en, args) ->
          let f (id, gc) = Printf.sprintf "(%s %d)" (show_id id) (share_glob_constr gc) in
          with_gc_idx glob_constr (Printf.sprintf "(E %s %s)" (show_id en) (show_sexpr_ls f args))
      | GPatVar (_, (b, pv)) ->
          with_gc_idx glob_constr (Printf.sprintf "(PV %b %s)" b (show_id pv))
      | GApp (_, gc, gcs) ->
          let idx = share_glob_constr gc in
          let idxs = share_glob_constrs gcs in
          begin match gc with
          | GRef (_, gr, _) ->
              let imps = implicits_of_global gr in
              let f (id, ie, (mi, fi)) = Printf.sprintf "(%s %s)" (show_id id) (show_implicit_explanation ie) in
              let iargs = (show_sexpr_ls (show_sexpr_ls (show_maybe f)) (List.map snd imps)) in
              with_gc_idx glob_constr (Printf.sprintf "(A %d %s %s)" idx idxs iargs)
          | _ -> with_gc_idx glob_constr (Printf.sprintf "(A %d %s ())" idx idxs)
          end
      | GLambda (_, n, bk, gc1, gc2) ->
          let sn = show_name n in
          let sbk = (show_binding_kind bk) in
          let idx1 = share_glob_constr gc1 in
          let idx2 = share_glob_constr gc2 in
          with_gc_idx glob_constr (Printf.sprintf "(L %s %s %d %d)" sn sbk idx1 idx2)
      | GProd (_, n, bk, gc1, gc2) ->
          let sn = show_name n in
          let sbk = (show_binding_kind bk) in
          let idx1 = share_glob_constr gc1 in
          let idx2 = share_glob_constr gc2 in
          with_gc_idx glob_constr (Printf.sprintf "(P %s %s %d %d)" sn sbk idx1 idx2)
      | GLetIn (_, n, gc1, gc2) ->
          let sn = show_name n in
          let idx1 = share_glob_constr gc1 in
          let idx2 = share_glob_constr gc2 in
          with_gc_idx glob_constr (Printf.sprintf "(LI %s %d %d)" sn idx1 idx2)
      | GCases (_, csty, m_gc, tups, ccs) ->
          let scsty = show_case_style csty in
          let sm_gc = show_maybe share_glob_constr' m_gc in
          let stups = show_tomatch_tuples share_glob_constr' tups in
          let sccs = show_case_clauses share_glob_constr' ccs in
          with_gc_idx glob_constr (Printf.sprintf "(C %s %s %s %s)" scsty sm_gc stups sccs)
      | GLetTuple (_, ns, arg, gc1, gc2) ->          
          let names = show_sexpr_ls show_name ns in
          let f (name, m_gc) = Printf.sprintf "(%s %s)" (show_name name) (show_maybe share_glob_constr' m_gc) in
          let idx1 = share_glob_constr gc1 in
          let idx2 = share_glob_constr gc2 in
          with_gc_idx glob_constr (Printf.sprintf "(LT %s %s %d %d)" names (f arg) idx1 idx2)      
      | GIf (_, gc, (n, m_gc), gc2, gc3) ->
          let idx = share_glob_constr gc in
          let o = Printf.sprintf "(%s %s)" (show_name n) (show_maybe share_glob_constr' m_gc) in
          let idx2 = share_glob_constr gc2 in
          let idx3 = share_glob_constr gc3 in
          with_gc_idx glob_constr (Printf.sprintf "(I %d %s %d %d)" idx o idx2 idx3)
      | GRec (_, fk, ids, gdss, gcs1, gcs2) ->
          let sfk = show_fix_kind share_glob_constr' fk in
          let sids = show_sexpr_arr show_id ids in
          let sgdss = show_sexpr_arr (show_sexpr_ls (show_glob_decl share_glob_constr')) gdss in
          let idxs1 = share_glob_constr_arr gcs1 in
          let idxs2 = share_glob_constr_arr gcs2 in
          with_gc_idx glob_constr (Printf.sprintf "(R %s %s %s %s %s)" sfk sids sgdss idxs1 idxs2)
      | GSort (_, gsort) ->
          with_gc_idx glob_constr (Printf.sprintf "(S %s)" (show_glob_sort gsort))
      | GHole (_, k, ipne, m_gga) ->
          with_gc_idx glob_constr (Printf.sprintf "(H %s %s %s)" (show_evar_kinds k) (show_intro_pattern_naming_expr ipne) (show_maybe show_generic_arg m_gga))
      | GCast (_, gc, gc_ty) ->
          let idx = share_glob_constr gc in
          let sgc_ty = show_cast_type share_glob_constr' gc_ty in
          with_gc_idx glob_constr (Printf.sprintf "(T %d %s)" idx sgc_ty)
and share_glob_constr' gc =
  string_of_int (share_glob_constr gc)
and share_glob_constrs gcs = 
  show_sexpr_ls (fun gc -> string_of_int (share_glob_constr gc)) gcs
and share_glob_constr_arr gcs = 
  show_sexpr_arr (fun gc -> string_of_int (share_glob_constr gc)) gcs



(* ************************************************************************** *)
(* Ltac printing *)

(* Note(deh): 
 *
 * A global term is a pair of
 * 1. a [glob_constr]
 * 2. an optional [constr_expr] that the glob_constr came from
 *
 *)


let show_gtrm (gc, m_c) =
  show_glob_constr gc

let show_may_eval mev =
  match mev with
  | ConstrEval (r, c) ->
      (* NOTE(deh): this TODO isn't necessary as it just tells the type of reduction? *)
      Printf.sprintf "(E %s %s)" "TODO" (show_gtrm c)
  | ConstrContext ((_, id), c) ->
      Printf.sprintf "(C %s %s)" (show_id id) (show_gtrm c)
  | ConstrTypeOf c ->
      Printf.sprintf "(T %s)" (show_gtrm c)
  | ConstrTerm c ->
      Printf.sprintf "(M %s)" (show_gtrm c)

let show_multi m =
  match m with
  | Precisely i -> Printf.sprintf "(P %d)" i
  | UpTo i -> Printf.sprintf "(U %d)" i
  | RepeatStar -> "*"
  | RepeatPlus -> "+"


let rec show_occurrences_gen f og =
  match og with
  | AllOccurrences -> "A"
  | AllOccurrencesBut ls -> Printf.sprintf "(B %s)" (show_sexpr_ls f ls)
  | NoOccurrences -> "N"
  | OnlyOccurrences ls -> Printf.sprintf "(O %s)" (show_sexpr_ls f ls)
and show_occurrences_expr oe =
  show_occurrences_gen (show_or_var string_of_int) oe
and show_with_occurrences show (oe, a) =
  Printf.sprintf "(%s %s)" (show_occurrences_expr oe) (show a)


let rec show_hyp_location_flag hlf =
  match hlf with
  | InHyp -> "H"
  | InHypTypeOnly -> "T"
  | InHypValueOnly -> "V"
and show_hyp_location_expr ((occs, gnm), hlf) =
  Printf.sprintf "(%s %s %s)" (show_occurrences_expr occs) (show_gname gnm) (show_hyp_location_flag hlf)
and show_clause_expr ce = 
  Printf.sprintf "(%s %s)" (show_maybe (fun x -> show_sexpr_ls show_hyp_location_expr x) ce.onhyps) (show_occurrences_expr ce.concl_occs)


let rec show_quantified_hypothesis qhyp = 
  match qhyp with
  | AnonHyp i -> Printf.sprintf "@%d" i
  | NamedHyp id -> show_id id
and show_explicit_binding' show_a (loc, qhyp, a) =
  Printf.sprintf "(%s %s)" (show_quantified_hypothesis qhyp) (show_a a)
and show_bindings show_a b =
  match b with
  | ImplicitBindings ls ->
      Printf.sprintf "(I %s)" (show_sexpr_ls show_a ls)
  | ExplicitBindings ebs ->
      Printf.sprintf "(E %s)" (show_sexpr_ls (show_explicit_binding' show_a) ebs)
  | NoBindings -> "N"
and show_with_bindings show_a (a, b) = 
  Printf.sprintf "(%s %s)" (show_a a) (show_bindings show_a b)
and show_with_bindings_arg show_a (cf, b) =
  Printf.sprintf "(%s %s)" (show_maybe string_of_bool cf) (show_with_bindings show_a b)


let rec show_destruction_arg show_a (cf, cda) =
  Printf.sprintf "(%s %s)" (show_maybe string_of_bool cf) (show_core_destruction_arg show_a cda)
and show_core_destruction_arg show_a cda =
  match cda with
  | ElimOnConstr a ->
      Printf.sprintf "(C %s)" (show_a a)
  | ElimOnIdent (loc, id) ->
      Printf.sprintf "(I %s)" (show_id id)
  | ElimOnAnonHyp i ->
      Printf.sprintf "(A %d)" i


let rec show_induction_clause (wbs_da, (ml_ipne, movl_oaipe), m_ce) =
  let f (loc, ipne) = show_intro_pattern_naming_expr ipne in
  let g (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
  let g' = show_maybe (show_or_var g) in
  Printf.sprintf "(%s %s %s %s)" (show_destruction_arg (show_with_bindings show_gtrm) wbs_da) (show_maybe f ml_ipne) (g' movl_oaipe) (show_maybe show_clause_expr m_ce)
and show_induction_clause_list (ics, m_bs) =
  Printf.sprintf "(%s, %s)" (show_sexpr_ls show_induction_clause ics) (show_maybe (show_with_bindings show_gtrm) m_bs)


let rec show_inversion_strength is =
  match is with
  | NonDepInversion (ik, gnms, movl_oaipe) ->
      let f (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
      let g = show_or_var f in
      Printf.sprintf "(NonDep %s %s %s)" (show_inversion_kind ik) (show_sexpr_ls show_gname gnms) (show_maybe g movl_oaipe)
  | DepInversion (ik, maybe_c, movl_oaipe) ->
      let f (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
      let g = show_or_var f in
      Printf.sprintf "(Dep %s %s %s)" (show_inversion_kind ik) (show_maybe show_gtrm maybe_c) ((show_maybe g movl_oaipe))
  | InversionUsing (c, gnms) ->
      Printf.sprintf "(Using %s %s)" (show_gtrm c) (show_sexpr_ls show_gname gnms)
and show_inversion_kind ik = 
  match ik with
  | SimpleInversion -> "S"
  | FullInversion -> "F"
  | FullInversionClear -> "FC"


let show_lazy_flag lf =
  match lf with
  | General -> "G"
  | Select -> "S"
  | Once -> "O"

let show_global_flag gf =
  match gf with
  | TacGlobal -> "G"
  | TacLocal -> "L"

let show_message_token mtok = 
  match mtok with
  | MsgString s -> Printf.sprintf "(S %s)" s
  | MsgInt i -> Printf.sprintf "(I %d)" i
  | MsgIdent gnm -> Printf.sprintf "(D %s)" (show_gname gnm)

let show_goal_selector gs =
  match gs with
  | SelectNth i ->
      Printf.sprintf "(N %d)" i
  | SelectList ls ->
      Printf.sprintf "(L %s)" (show_sexpr_ls (fun (i, j) -> Printf.sprintf "(%d %d)" i j) ls)
  | SelectId id ->
      Printf.sprintf "(I %s)" (show_id id)
  | SelectAll -> "A"


let rec show_match_rule show_pat show_tac mrule =
  match mrule with
  | Pat (hyps, pat, tac) ->
      Printf.sprintf "(P %s %s %s)" (show_sexpr_ls (show_match_context_hyps show_pat) hyps) (show_match_pattern show_pat pat) (show_tac tac)
  | All tac ->
      Printf.sprintf "(A %s)" (show_tac tac)
and show_match_rules show_pat show_tac mrules =
  show_sexpr_ls (show_match_rule show_pat show_tac) mrules
and show_match_pattern show_pat mp =
  match mp with
  | Term p -> Printf.sprintf "(T %s)" (show_pat p)
  | Subterm (b, maybe_id, p) ->
      Printf.sprintf "(S %b %s %s)" b (show_maybe show_id maybe_id) (show_pat p)
and show_match_context_hyps show_pat hyps =
  match hyps with
  | Hyp ((loc, name), mp) ->
      Printf.sprintf "(H %s %s)" (show_name name) (show_match_pattern show_pat mp)
  | Def ((loc, name), mp1, mp2) ->
      Printf.sprintf "(D %s %s %s)" (show_name name) (show_match_pattern show_pat mp1) (show_match_pattern show_pat mp2)


let show_ml_tactic_entry mlen =
  let name = mlen.mltac_name in
  Printf.sprintf "(%s %s %d)" name.mltac_plugin name.mltac_tactic mlen.mltac_index


let rec show_constr_pattern cp =
  match cp with
  | Pattern.PRef gr ->
      Printf.sprintf "(! %s)" (show_global_reference gr)
  | Pattern.PVar id ->
      Printf.sprintf "(V %s)" (show_id id)
  | Pattern.PEvar (ek, cps) ->
      Printf.sprintf "(E %d %s)" (show_evar ek) (show_sexpr_arr show_constr_pattern cps)
  | Pattern.PRel i ->
      Printf.sprintf "(R %d)" i
  | Pattern.PApp (cp, cps) ->
      Printf.sprintf "(A %s %s)" (show_constr_pattern cp) (show_sexpr_arr show_constr_pattern cps)
  | Pattern.PSoApp (pv, cps) ->
      Printf.sprintf "(SA %s %s)" (show_constr_pattern cp) (show_sexpr_ls show_constr_pattern cps) 
  | Pattern.PProj (proj, cp) ->
      Printf.sprintf "(PJ %s %s)" (Names.Projection.to_string proj) (show_constr_pattern cp)
  | Pattern.PLambda (name, cp1, cp2) ->
      Printf.sprintf "(L %s %s %s)" (show_name name) (show_constr_pattern cp1) (show_constr_pattern cp2)
  | Pattern.PProd (name, cp1, cp2) ->
      Printf.sprintf "(P %s %s %s)" (show_name name) (show_constr_pattern cp1) (show_constr_pattern cp2)
  | Pattern.PLetIn (name, cp1, cp2) ->
      Printf.sprintf "(LI %s %s %s)" (show_name name) (show_constr_pattern cp1) (show_constr_pattern cp2)
  | Pattern.PSort gs ->
      Printf.sprintf "(S %s)" (show_glob_sort gs)
  | Pattern.PMeta m_pv ->
      Printf.sprintf "(M %s)" (show_maybe show_id m_pv)
  | Pattern.PIf (cp1, cp2, cp3) ->
      Printf.sprintf "(I %s %s %s)" (show_constr_pattern cp1) (show_constr_pattern cp2) (show_constr_pattern cp3)
  | Pattern.PCase (cip, cp1, cp2, ls) ->
      (* NOTE(deh): this TODO is a case pattern style which isn't necessary? *)
      let f (i, bs, cp) = Printf.sprintf "(%d %s %s)" i (show_sexpr_ls string_of_bool bs) (show_constr_pattern cp) in
      Printf.sprintf "(C %s %s %s %s)" "TODO" (show_constr_pattern cp1) (show_constr_pattern cp2) (show_sexpr_ls f ls)
  | Pattern.PFix fix ->
      let f ((is, i), rd) = Printf.sprintf "(%s %d %s)" (show_sexpr_arr string_of_int is) i (show_rec_declaration rd) in
      Printf.sprintf "(F %s)" (f fix)
  | Pattern.PCoFix cofix ->
      let f (i, rd) = Printf.sprintf "(%d %s)" i (show_rec_declaration rd) in
      Printf.sprintf "(CF %s)" (f cofix)
and show_rec_declaration (names, tys, cs) = 
  Printf.sprintf "(%s %s %s)" (show_sexpr_arr show_name names) (show_sexpr_arr show_constr tys) (show_sexpr_arr show_constr cs) 


let rec show_tactic_arg ta =
  match ta with
  | TacGeneric ga ->
      Printf.sprintf "(G %s)" (show_generic_arg ga)
  | ConstrMayEval mev ->
      Printf.sprintf "(ME %s)" (show_may_eval mev)
  | Reference r ->
      Printf.sprintf "(R %s)" (show_g_reference r)
  | TacCall (loc, r, targs) ->
      Printf.sprintf "(C %s %s)" (show_g_reference r) (show_tactic_args targs)
  | TacFreshId sovs ->
      Printf.sprintf "(F %s)" (show_sexpr_ls (fun x -> show_or_var (fun x -> x) x) sovs)
  | Tacexp tac ->
      Printf.sprintf "(E %s)" (show_tac tac)
  | TacPretype c ->
      Printf.sprintf "(P %s)" (show_gtrm c)
  | TacNumgoals -> "N"
and show_tactic_args tas = 
  show_sexpr_ls show_tactic_arg tas

and show_atomic_tac atac =
  match atac with
  | TacIntroPattern (ef, ipes) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      Printf.sprintf "(IntroPattern %b %s)" ef (show_sexpr_ls f ipes)
  | TacApply (af, ef, bargss, gnm_and_ipe) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      let g (gnm, x) = Printf.sprintf "(%s %s)" (show_gname gnm) (show_maybe f x) in
      Printf.sprintf "(Apply %b %b %s %s)" af ef (show_sexpr_ls (show_with_bindings_arg show_gtrm) bargss) (show_maybe g gnm_and_ipe)
  | TacElim (ef, bargs, maybe_wb) ->
      Printf.sprintf "(Elim %b %s %s)" ef (show_with_bindings_arg show_gtrm bargs) (show_maybe (show_with_bindings show_gtrm) maybe_wb)
  | TacCase (ef, bargs) ->
      Printf.sprintf "(Case %b %s)" ef (show_with_bindings_arg show_gtrm bargs)
  | TacMutualFix (id, i, body) ->
      let f (id, i, c) = Printf.sprintf "(%s %d %s)" (show_id id) i (show_gtrm c) in
      Printf.sprintf "(MutualFix %s %d %s)" (show_id id) i (show_sexpr_ls f body)
  | TacMutualCofix (id, body) ->
      let f (id, c) = Printf.sprintf "(%s, %s)" (show_id id) (show_gtrm c) in
      Printf.sprintf "(MutualCofix %s %s)" (show_id id) (show_sexpr_ls f body)
  | TacAssert (b, mm_tac, ml_ipe, c) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      let g = show_maybe f in
      Printf.sprintf "(Assert %b %s %s %s)" b (show_maybe (show_maybe show_tac) mm_tac) (g ml_ipe) (show_gtrm c)
  | TacGeneralize ls ->
      let f (wo, name) = Printf.sprintf "(%s %s)" (show_with_occurrences show_gtrm wo) (show_name name) in
      Printf.sprintf "(Generalize %s)" (show_sexpr_ls f ls)
  | TacLetTac (name, c, ce, lf, ml_ipe) ->
      let f (loc, ipne) = show_intro_pattern_naming_expr ipne in
      Printf.sprintf "(LetTac %s %s %s %b %s)" (show_name name) (show_gtrm c) (show_clause_expr ce) lf (show_maybe f ml_ipe)
  | TacInductionDestruct (rf, ef, ics) ->
      Printf.sprintf "(InductionDestruct %b %b %s)" rf ef (show_induction_clause_list ics)
  | TacReduce (reg, ce) ->
      (* NOTE(deh): this TODO isn't necessary as it just tells the type of reduction? *)
      Printf.sprintf "(Reduce %s %s)" "TODO" (show_clause_expr ce)
  | TacChange (maybe_pat, dtrm, ce) ->
      let f (_, gtrm, cpat) = show_gtrm gtrm in
      Printf.sprintf "(Change %s %s %s)" (show_maybe f maybe_pat) (show_gtrm dtrm) (show_clause_expr ce)
  | TacRewrite (ef, rargs, ce, maybe_tac) ->
      let f (b, m, barg) = Printf.sprintf "(%b %s %s)" b (show_multi m) (show_with_bindings_arg show_gtrm barg) in
      Printf.sprintf "(Rewrite %b %s %s %s)" ef (show_sexpr_ls f rargs) (show_clause_expr ce) (show_maybe show_tac maybe_tac)
  | TacInversion (is, qhyp) ->
      Printf.sprintf "(Inversion %s %s)" (show_inversion_strength is) (show_quantified_hypothesis qhyp)

and show_tac tac =
  match tac with
  | TacAtom (loc, atac) ->
      Printf.sprintf "(Atom %s)" (show_atomic_tac atac)
  | TacThen (tac1, tac2) ->
      Printf.sprintf "(Then %s %s)" (show_tac tac1) (show_tac tac2)
  | TacDispatch tacs ->
      Printf.sprintf "(Dispatch %s)" (show_tacs tacs)
  | TacExtendTac (tacs1, tac, tacs2) ->
      Printf.sprintf "(ExtendTac %s %s %s)" (show_tac_arr tacs1) (show_tac tac) (show_tac_arr tacs2)
  | TacThens (tac, tacs) ->
      Printf.sprintf "(Thens %s %s)" (show_tac tac) (show_tacs tacs)
  | TacThens3parts (tac1, tac1s, tac2, tac2s) ->
      Printf.sprintf "(Thens3parts %s %s %s %s)" (show_tac tac1) (show_tac_arr tac1s) (show_tac tac2) (show_tac_arr tac2s)
  | TacFirst tacs ->
      Printf.sprintf "(First %s)" (show_tacs tacs)
  | TacComplete tac ->
      Printf.sprintf "(Complete %s)" (show_tac tac)
  | TacSolve tacs ->
      Printf.sprintf "(Solve %s)" (show_tacs tacs)
  | TacTry tac ->
      Printf.sprintf "(Try %s)" (show_tac tac)
  | TacOr (tac1, tac2) ->
      Printf.sprintf "(Or %s %s)" (show_tac tac1) (show_tac tac2)
  | TacOnce tac ->
      Printf.sprintf "(Once %s)" (show_tac tac)
  | TacExactlyOnce tac ->
      Printf.sprintf "(ExactlyOnce %s)" (show_tac tac)
  | TacIfThenCatch (tac1, tac2, tac3) ->
      Printf.sprintf "(IfThenCatch %s %s %s)" (show_tac tac1) (show_tac tac2) (show_tac tac3)
  | TacOrelse (tac1, tac2) ->
      Printf.sprintf "(Orelse %s %s)" (show_tac tac1) (show_tac tac2)
  | TacDo (iov, tac) ->
      Printf.sprintf "(Do %s %s)" (show_or_var string_of_int iov) (show_tac tac)
  | TacTimeout (iov, tac) ->
      Printf.sprintf "(Timeout %s %s)" (show_or_var string_of_int iov) (show_tac tac)
  | TacTime (maybe_str, tac) ->
      Printf.sprintf "(Time %s %s)" (show_maybe (fun x -> x) maybe_str) (show_tac tac)
  | TacRepeat tac ->
      Printf.sprintf "(Repeat %s)" (show_tac tac)
  | TacProgress tac ->
      Printf.sprintf "(Progress %s)" (show_tac tac)
  | TacShowHyps tac ->
      Printf.sprintf "(ShowHyps %s)" (show_tac tac)
  | TacAbstract (tac, maybe_id) ->
      Printf.sprintf "(Abstract %s %s)" (show_tac tac) (show_maybe show_id maybe_id)
  | TacId msgs ->
      Printf.sprintf "(Id %s)" (show_sexpr_ls show_message_token msgs)
  | TacFail (gf, iov, msgs) ->
      Printf.sprintf "(Fail %s %s %s)" (show_global_flag gf) (show_or_var string_of_int iov) (show_sexpr_ls show_message_token msgs)
  | TacInfo tac ->
      Printf.sprintf "(Info %s)" (show_tac tac)
  | TacLetIn (rf, bindings, tac) ->
      let f ((loc, id), targ) = Printf.sprintf "(%s %s)" (show_id id) (show_tactic_arg targ) in
      Printf.sprintf "(Let %b %s %s)" rf (show_sexpr_ls f bindings) (show_tac tac)
  | TacMatch (lf, tac, mrules) ->
      let show_pat (bbvs, gtrm, cpat) = Printf.sprintf "(%s %s %s)" (show_sexpr_ls show_id (Id.Set.elements bbvs)) (show_gtrm gtrm) (show_constr_pattern cpat) in
      Printf.sprintf "(Match %s %s %s)" (show_lazy_flag lf) (show_tac tac) (show_match_rules show_pat show_tac mrules)
  | TacMatchGoal (lf, df, mrules) ->
      let show_pat (bbvs, gtrm, cpat) = Printf.sprintf "(%s %s %s)" (show_sexpr_ls show_id (Id.Set.elements bbvs)) (show_gtrm gtrm) (show_constr_pattern cpat) in
      Printf.sprintf "(MatchGoal %s %b %s)" (show_lazy_flag lf) df (show_match_rules show_pat show_tac mrules)
  | TacFun (maybe_ids, tac) ->
      Printf.sprintf "(Fun %s %s)" (show_sexpr_ls (show_maybe show_id) maybe_ids) (show_tac tac)
  | TacArg (loc, targ) ->
      Printf.sprintf "(Arg %s)" (show_tactic_arg targ)
  | TacSelect (gs, tac) ->
      Printf.sprintf "(Select %s %s)" (show_goal_selector gs) (show_tac tac)
  | TacML (loc, mlen, targs) ->
      Printf.sprintf "(ML %s %s)" (show_ml_tactic_entry mlen) (show_tactic_args targs)
  | TacAlias (loc, kername, targs) ->
      Printf.sprintf "(Alias %s %s)" (KerName.to_string kername) (show_tactic_args targs)
and show_tacs tacs =
  show_sexpr_ls show_tac tacs
and show_tac_arr tacs = 
  show_sexpr_arr show_tac tacs



(* ************************************************************************** *)
(* Context printing *)

(* NOTE(deh): 
 * 
 * 1. Tactic state is list of pairs of identifiers and expression integers (from sharing)
 *    x1 5, x2 10, x3 2, ... {!} 4
 *
 * 2. Pretty-print information
 *    tacst_ctx_ppM: int -> pp_str        (map shared id to pretty-print string)
 *
 * 3. glob_constr information
 *    tacst_ctx_gcM: int -> glob_constr   (map shared it to glob_constr)
 *)

let tacst_ctx_ppM : (int * string * string option) IntMap.t ref = ref IntMap.empty
let clear_tacst_ctx_ppM () = tacst_ctx_ppM := IntMap.empty
let add_tacst_ctx_ppM key value = tacst_ctx_ppM := IntMap.add key value !tacst_ctx_ppM
let dump_pretty_tacst_ctx_gcM () =
  let f k v =
    match v with
    | (gc_idx, _, _) -> ml4tp_write (Printf.sprintf "%d: %d\n" k gc_idx)
  in
  IntMap.iter f !tacst_ctx_ppM
let dump_pretty_tacst_ctx_typM () =
  let f k v =
    match v with
    | (_, pp_typ, _) -> ml4tp_write (Printf.sprintf "%d: %s\n" k pp_typ)
  in
  IntMap.iter f !tacst_ctx_ppM
let dump_pretty_tacst_ctx_bodyM () =
  let f k v =
    match v with
    | (_, _, Some pp_body) -> ml4tp_write (Printf.sprintf "%d: %s\n" k pp_body)
    | (_, _, None) -> ()
  in
  IntMap.iter f !tacst_ctx_ppM

(* NOTE(deh): switch for hashtable *)
(*
let tacst_ctx_ppM = IntTbl.create 500
let clear_tacst_ctx_ppM () = IntTbl.clear tacst_ctx_ppM
let add_tacst_ctx_ppM key value = IntTbl.add tacst_ctx_ppM key value
let dump_pretty_tacst_ctx_typM () =
  let f k v =
    match v with
    | (pp_typ, _) -> ml4tp_write (Printf.sprintf "%d: %s\n" k pp_typ)
  in
  IntTbl.iter f tacst_ctx_ppM
let dump_pretty_tacst_ctx_bodyM () =
  let f k v =
    match v with
    | (_, Some pp_body) -> ml4tp_write (Printf.sprintf "%d: %s\n" k pp_body)
    | (_, None) -> ()
  in
  IntTbl.iter f tacst_ctx_ppM
*)

let detype env sigma constr = 
  let avoid = Termops.ids_of_context env in
  Detyping.detype ~lax:false true avoid env sigma constr

(*
let show_ctx_ldecl env sigma (typ, pr_typ, body) id =
  match body with
  | Some (body, pp_body) ->
      let typ_id = share_constr typ in 
      let body_id = share_constr body in
      let typ_gc = show_glob_constr (detype env sigma typ) in
      add_tacst_ctx_ppM typ_id (typ_gc, pr_typ, Some pp_body);
      Printf.sprintf "%s %d %d" (show_id id) typ_id body_id
  | None ->
      let typ_id = share_constr typ in
      let typ_gc = show_glob_constr (detype env sigma typ) in
      add_tacst_ctx_ppM typ_id (typ_gc, pr_typ, None);
      Printf.sprintf "%s %d" (show_id id) typ_id
*)

(* NOTE(deh): experimental *)
let show_ctx_ldecl' env sigma (typ, body) id =
  let typ_id = share_constr typ in
  match IntMap.find_opt typ_id !tacst_ctx_ppM with
  | Some (gc_typ_id, _, _) ->
      Printf.sprintf "%s %d %d" (show_id id) typ_id gc_typ_id
  | None -> 
      let gc_typ_id = share_glob_constr (detype env sigma typ) in
      let pr_typ = pp2str (pr_ltype_env env sigma typ) in
      add_tacst_ctx_ppM typ_id (gc_typ_id, pr_typ, None);
      Printf.sprintf "%s %d %d" (show_id id) typ_id gc_typ_id
  (*
  if IntMap.mem typ_id !tacst_ctx_ppM
  then Printf.sprintf "%s %d" (show_id id) typ_id
  else
    let typ_gc = share_glob_constr (detype env sigma typ) in
    let pr_typ = pp2str (pr_ltype_env env sigma typ) in
    add_tacst_ctx_ppM typ_id (typ_gc, pr_typ, None);
    Printf.sprintf "%s %d" (show_id id) typ_id
  *)
      
let show_var_list_decl env sigma (l, c, typ) =
  let pbody = match c with
    | None -> None
    | Some c ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        Some (c, pp2str pb)
  in
  (* List.map (show_ctx_ldecl env sigma (typ, pp2str (pr_ltype_env env sigma typ), pbody)) l *)
  List.map (show_ctx_ldecl' env sigma (typ, pbody)) l

let show_rel_decl env sigma decl =
  let open Context.Rel.Declaration in
  let na = get_name decl in
  let typ = get_type decl in
  let id = 
    match na with
    | Anonymous -> Names.Id.of_string (show_name na)
    | Name id -> id
  in
  let body = 
    match decl with
    | LocalAssum _ -> None
    | LocalDef (_, c, _) ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        Some (c, pp2str pb)
  in
  (* show_ctx_ldecl env sigma (typ, pp2str (pr_ltype_env env sigma typ), body) id *)
  show_ctx_ldecl' env sigma (typ, body) id

let show_context env sigma =
  let named_ids =
    Context.NamedList.fold
      (fun decl ids -> let ids' = show_var_list_decl env sigma decl in ids' @ ids)
      (Termops.compact_named_context (Environ.named_context env)) ~init:[]
  in
  let rel_ids = 
    Environ.fold_rel_context
      (fun env decl acc -> let r = show_rel_decl env sigma decl in r::acc)
      env ~init:[]
  in
  show_ls (fun x -> x) ", " (named_ids @ rel_ids)



(* ************************************************************************** *)
(* Goals printing *)

let tacst_goalM = ref IntMap.empty
let clear_tacst_goalM () = tacst_goalM := IntMap.empty
let add_goal cid env sigma concl =
  tacst_goalM := IntMap.add cid (pp2str (pr_goal_concl_style_env env sigma concl)) !tacst_goalM
let add_goal' env sigma concl = 
  let concl_id = share_constr concl in
  (*
  if IntMap.mem concl_id !tacst_goalM 
  then concl_id
  else
    let gc_concl = share_glob_constr (detype env sigma concl) in
    let pr_concl = pp2str (pr_goal_concl_style_env env sigma concl) in
    add_tacst_ctx_ppM concl_id (gc_concl, pr_concl, None);
    tacst_goalM := IntMap.add concl_id pr_concl !tacst_goalM;
    concl_id
  *)
  match IntMap.find_opt concl_id !tacst_ctx_ppM with
  | Some (gc_concl, _, _) -> (concl_id, gc_concl)
  | None ->
      let gc_concl = share_glob_constr (detype env sigma concl) in
      let pr_concl = pp2str (pr_goal_concl_style_env env sigma concl) in
      add_tacst_ctx_ppM concl_id (gc_concl, pr_concl, None);
      tacst_goalM := IntMap.add concl_id pr_concl !tacst_goalM;
      (concl_id, gc_concl)

(* NOTE(deh): No print because it's in shareM *)
let dump_pretty_tacst_goalM () = 
  IntMap.iter (fun k v -> ml4tp_write (Printf.sprintf "%d: %s\n" k v)) !tacst_goalM

(* NOTE(deh): switch for hashtable *)
(*
let tacst_goalM = IntTbl.create 500
let clear_tacst_goalM () = IntTbl.clear tacst_goalM
let add_goal cid env sigma concl =
  IntTbl.add tacst_goalM cid (pp2str (pr_goal_concl_style_env env sigma concl))
let dump_pretty_tacst_goalM () = 
  IntTbl.iter (fun k v -> ml4tp_write (Printf.sprintf "%d: %s\n" k v)) tacst_goalM
*)



(* ************************************************************************** *)
(* Incremental printing *)

(* NOTE(deh): 
 * 
 * For interactive proof-building, we need to output the shared representation
 * table after each proof step, not just at the end. Of course, we only output
 * the new entries.
 *)


(* Set to true if you want to have incremental output *)
let f_incout = ref true
let set_incout b = f_incout := b

(* Keep track of outputted shared ASTs *)
(*
let outputted_constrS = ref (IntSet.empty)
let clear_outputted_constrS () = outputted_constrS := IntSet.empty
let dump_outputted_constrS () =
  IntSet.iter (fun k -> ml4tp_write (Printf.sprintf "%d " k)) !outputted_constrS

let outputted_gcS = ref IntSet.empty
let clear_outputted_gcS () = outputted_gcS := IntSet.empty
*)

let dump_low_incr_constrM () =
  (*
  let f constr_idx constr_val =
    if IntSet.mem constr_idx !outputted_constrS
    then ()
    else begin
      (* Output constr table *)
      outputted_constrS := IntSet.add constr_idx !outputted_constrS;
      ml4tp_write (Printf.sprintf "%d: %s\n" constr_idx constr_val)
    end
  in
  *)
  if !f_incout
  then begin
    ml4tp_write "bg(inc)\n";
    List.iter (fun (gc_idx, gc_val) -> ml4tp_write (Printf.sprintf "%d: %s\n" gc_idx gc_val)) (List.rev !new_low_gcs);
    ml4tp_write "Constrs\n";
    List.iter (fun (constr_idx, constr_val) -> ml4tp_write (Printf.sprintf "%d: %s\n" constr_idx constr_val)) (List.rev !new_low_constrs);
    (* IntMap.iter f !tacst_low_constrM; *)
    (* NOTE(deh): switch for hashtable *)
    (* IntTbl.iter f tacst_low_constrM; *)
    ml4tp_write "en(inc)\n"
  end
  else ();
  clear_new_low_constrs ();
  clear_new_low_gcs ()



(* ************************************************************************** *)
(* Begin/End Proof *)

let initialize_proof () =
  GenSym.reset gs_callid;
  GenSym.reset gs1;
  GenSym.reset gs2;
  GenSym.reset gs3;
  GenSym.reset gs4;
  GenSym.reset gs_constridx;
  GenSym.reset gs_gc_idx;
  GenSym.reset gs_anon;
  clear_tacst_ctx_ppM ();
  clear_tacst_goalM ();
  clear_constr_shareM ();
  clear_tacst_low_constrM ();
  (* clear_outputted_constrS (); *)
  clear_gc_shareM ();
  clear_tacst_low_gcM ()
  (* clear_outputted_gcS () *)

let finalize_proof () =
  ml4tp_write "Constrs\n";
  dump_low_constrM ();
  ml4tp_write "PrTyps\n";
  dump_pretty_tacst_ctx_typM ();
  ml4tp_write "PrBods\n";
  dump_pretty_tacst_ctx_bodyM ();
  ml4tp_write "PrGls\n";
  dump_pretty_tacst_goalM ();
  ml4tp_flush()

let rec show_vernac_typ_exp vt ve =
  match vt with
  | VtStartProof (name, _, names) -> 
      initialize_proof ();
      ml4tp_write (Printf.sprintf "bg(pf) {!} %s {!} %s\n" name (show_ls show_id ", " names))
  | VtSideff _ -> ()
  | VtQed _ ->
      finalize_proof ();
      ml4tp_write ("en(pf)\n")
  | VtProofStep _ ->
    begin
      match ve with
      | VernacSubproof _ -> ml4tp_write "bg(spf)\n"
      | VernacEndSubproof -> ml4tp_write "en(spf)\n"
      | _ -> ()
    end
  | VtProofMode _ -> ()
  | VtQuery (_, _) -> ()
  | VtStm (_, _) -> ()
  | VtUnknown -> ()



(* ************************************************************************** *)
(* Junk *)

(*
let show_red_expr_gen show_a show_b show_c reg =
  match reg with
  | Red b -> Printf.sprintf "(R %b)" b
  | Hnf -> ""
  | Simpl _ -> ""
  | Cbv _ -> ""
  | Cbn _ -> ""
  | Lazy _ -> ""
  | Unfold _ -> ""
  | Fold _ -> ""
  | Pattern _ -> ""
  | ExtraRedExpr _ -> ""
  | CbvVm _ -> ""
  | CbvNative _ -> ""
*)
