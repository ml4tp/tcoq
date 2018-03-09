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

let with_constr_idx constr value =
  let idx = fresh_constridx () in
  ConstrHashtbl.add (constr_shareM) constr idx;
  tacst_low_constrM := IntMap.add idx value !tacst_low_constrM;
  (* NOTE(deh): switch for hashtable *)
  (* IntTbl.add tacst_low_constrM idx value; *)
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
(* Goals printing *)

let tacst_goalM = ref IntMap.empty
let clear_tacst_goalM () = tacst_goalM := IntMap.empty
let add_goal cid env sigma concl =
  tacst_goalM := IntMap.add cid (pp2str (pr_goal_concl_style_env env sigma concl)) !tacst_goalM
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
(* Context printing *)

(* NOTE(deh): 
 * 
 * 1. Tactic state is list of pairs of identifiers and expression integers (from sharing)
 *    x1 5, x2 10, x3 2, ... {!} 4
 *
 * 2. Pretty-print information
 *    tacst_ctx_ppM: int -> pp_str  (map shared id to pretty-print string)
 *)

let tacst_ctx_ppM = ref IntMap.empty
let clear_tacst_ctx_ppM () = tacst_ctx_ppM := IntMap.empty
let add_tacst_ctx_ppM key value = tacst_ctx_ppM := IntMap.add key value !tacst_ctx_ppM
let dump_pretty_tacst_ctx_typM () =
  let f k v =
    match v with
    | (pp_typ, _) -> ml4tp_write (Printf.sprintf "%d: %s\n" k pp_typ)
  in
  IntMap.iter f !tacst_ctx_ppM
let dump_pretty_tacst_ctx_bodyM () =
  let f k v =
    match v with
    | (_, Some pp_body) -> ml4tp_write (Printf.sprintf "%d: %s\n" k pp_body)
    | (_, None) -> ()
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

let show_ctx_ldecl (typ, pr_typ, body) id =
  match body with
  | Some (body, pp_body) ->
      let typ_id = share_constr typ in 
      let body_id = share_constr body in
      add_tacst_ctx_ppM typ_id (pr_typ, Some pp_body);
      Printf.sprintf "%s %d %d" (show_id id) typ_id body_id
  | None ->
      let typ_id = share_constr typ in
      add_tacst_ctx_ppM typ_id (pr_typ, None);
      Printf.sprintf "%s %d" (show_id id) typ_id

let show_var_list_decl env sigma (l, c, typ) =
  let pbody = match c with
    | None -> None
    | Some c ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        Some (c, pp2str pb)
  in
  List.map (show_ctx_ldecl (typ, pp2str (pr_ltype_env env sigma typ), pbody)) l

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
  show_ctx_ldecl (typ, pp2str (pr_ltype_env env sigma typ), body) id

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
(* Incremental printing *)

(* NOTE(deh): 
 * 
 * For interactive proof-building, we need to output the shared representation
 * table after each proof step, not just at the end. Of course, We output only
 * the new entries.
 *)


(* Set to true if you want to have incremental output *)
let f_incout = ref true
let set_incout b = f_incout := b

(* Keep track of outputted shared ASTs *)
module IntSet = Set.Make(struct type t = int let compare = compare end)
let outputted_constrS = ref (IntSet.empty)
let clear_outputted_constrS () = outputted_constrS := IntSet.empty
let dump_outputted_constrS () =
  IntSet.iter (fun k -> ml4tp_write (Printf.sprintf "%d " k)) !outputted_constrS

let dump_low_incr_constrM () =
  let f k v =
    if IntSet.mem k !outputted_constrS
    then ()
    else (outputted_constrS := IntSet.add k !outputted_constrS;
          ml4tp_write (Printf.sprintf "%d: %s\n" k v))
  in
  if !f_incout
  then
    (ml4tp_write "bg(inc)\n";
     IntMap.iter f !tacst_low_constrM;
     (* NOTE(deh): switch for hashtable *)
     (* IntTbl.iter f tacst_low_constrM; *)
     ml4tp_write "en(inc)\n")
  else ()



(* ************************************************************************** *)
(* Begin/End Proof *)

let initialize_proof () =
  GenSym.reset gs_callid;
  GenSym.reset gs1;
  GenSym.reset gs2;
  GenSym.reset gs3;
  GenSym.reset gs4;
  GenSym.reset gs_constridx;
  GenSym.reset gs_anon;
  clear_tacst_ctx_ppM ();
  clear_tacst_goalM ();
  clear_constr_shareM ();
  clear_tacst_low_constrM ();
  clear_outputted_constrS ()

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


let rec show_glob_constr gc =
  match gc with
  | GRef (l, gr, _) ->
      Printf.sprintf "(! %s)" (show_global_reference gr)
  | GVar (l, id) ->
      Printf.sprintf "(V %s)" (show_id id)
  | GEvar (l, en, args) -> 
      let f (id, gc) = Printf.sprintf "(%s, %s)" (show_id id) (show_glob_constr gc) in
      Printf.sprintf "(E %s %s)" (show_id en) (show_sexpr_ls f args)
  | GPatVar (l, (b, pv)) ->
      Printf.sprintf "(PV %b %s)" b (show_id pv)
  | GApp (l, gc, gcs) ->
      Printf.sprintf "(A %s %s)" (show_glob_constr gc) (show_glob_constrs gcs)
  | GLambda (l, n, bk, gc1, gc2) ->
      Printf.sprintf "(L %s %s %s %s)" (show_name n) (show_binding_kind bk) (show_glob_constr gc1) (show_glob_constr gc2)
  | GProd (l, n, bk, gc1, gc2) ->
      Printf.sprintf "(P %s %s %s %s)" (show_name n) (show_binding_kind bk) (show_glob_constr gc1) (show_glob_constr gc2)
  | GLetIn (l, n, gc1, gc2) ->
      Printf.sprintf "(LI %s %s %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
  | GCases (l, csty, m_gc, tups, ccs) ->
      Printf.sprintf "(C %s %s %s %s)" (show_case_style csty) (show_maybe show_glob_constr m_gc) (show_tomatch_tuples tups) (show_case_clauses ccs)
  | GLetTuple (l, ns, arg, gc1, gc2) ->
      let f (name, m_gc) = Printf.sprintf "(%s %s)" (show_name name) (show_maybe show_glob_constr m_gc) in
      Printf.sprintf "(LT %s %s %s %s)" (show_sexpr_ls show_name ns) (f arg) (show_glob_constr gc1) (show_glob_constr gc2)
  | GIf (l, gc, (n, m_gc), gc2, gc3) ->
      Printf.sprintf "(I %s %s %s)" (show_glob_constr gc) (show_glob_constr gc2) (show_glob_constr gc3)
  | GRec (l, fk, ids, gdss, gcs1, gcs2) ->
      Printf.sprintf "(R %s %s %s %s %s)" (show_fix_kind fk) (show_sexpr_arr show_id ids) (show_sexpr_arr (show_sexpr_ls show_glob_decl) gdss) (show_glob_constr_arr gcs1) (show_glob_constr_arr gcs2)
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

and show_predicate_pattern (n, m_args) =
  let f (loc, (mutind, i), ns) = Printf.sprintf "(%s %d %s)" (Names.MutInd.to_string mutind) i (show_sexpr_ls show_name ns) in
  Printf.sprintf "(%s %s)" (show_name n) (show_maybe f m_args)
and show_tomatch_tuple (gc, pp) =
  Printf.sprintf "(%s %s)" (show_glob_constr gc) (show_predicate_pattern pp)
and show_tomatch_tuples tmts =
  show_sexpr_ls show_tomatch_tuple tmts

and show_case_clause (loc, ids, cps, gc) = 
  Printf.sprintf "(%s %s %s)" (show_sexpr_ls show_id ids) (show_sexpr_ls show_cases_pattern cps) (show_glob_constr gc)
and show_case_clauses ccs =
  show_sexpr_ls show_case_clause ccs

and show_fix_recursion_order fro =
  match fro with
  | GStructRec ->
      "S"
  | GWfRec gc ->
      Printf.sprintf "(W %s)" (show_glob_constr gc)
  | GMeasureRec (gc, m_gc) ->
      Printf.sprintf "(M %s %s)" (show_glob_constr gc) (show_maybe show_glob_constr m_gc)
and show_fix_kind fk =
  match fk with
  | GFix (ifros, i) ->
      let f (m_j, fro) = Printf.sprintf "(%s %s)" (show_maybe string_of_int m_j) (show_fix_recursion_order fro) in
      Printf.sprintf "(F %s %d)" (show_sexpr_arr f ifros) i
  | GCoFix i ->
      Printf.sprintf "(C %d)" i
and show_glob_decl (name, bk, m_c, c) =
  Printf.sprintf "%s %s %s %s" (show_name name) (show_binding_kind bk) (show_maybe show_glob_constr m_c) (show_glob_constr c)


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
