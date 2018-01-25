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

(* [Note] 
 *
 * Contains functionality for ML4TP. Prints out the tactic state of a Coq proof.
 * We output a "shared" representation of a Coq tactic state.
 *   1. Low-level format of expressions uses sharing
 *   2. Low-level format of tactic states just outputs identifiers and goal index
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



(* ************************************************************************** *)
(* Utility functions *)

(* Showing *)

let show_ls f sep ls =
  String.concat sep (List.map f ls)

let show_arr f sep arr =
  let arr' = Array.map f arr in
  String.concat sep (Array.to_list arr')

let brackets s = Printf.sprintf "[%s]" s

let show_maybe f maybe =
  match maybe with
  | None -> "N"
  | Some x -> Printf.sprintf "S(%s)" (f x)

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
  | ArgArg x -> f x 
  | ArgVar (loc, id) -> show_id id

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
(*
let tacst_low_constrM = IntTbl.create 2000
let clear_tacst_low_constrM () = IntTbl.clear tacst_low_constrM
let dump_low_constrM () = 
  IntTbl.iter (fun k v -> ml4tp_write (Printf.sprintf "%d: %s\n" k v)) tacst_low_constrM
*)

let with_constr_idx constr value =
  let idx = fresh_constridx () in
  ConstrHashtbl.add (constr_shareM) constr idx;
  tacst_low_constrM := IntMap.add idx value !tacst_low_constrM;
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
(*
let tacst_goalM = IntTbl.create 500
let clear_tacst_goalM () = IntTbl.clear tacst_goalM
let add_goal cid env sigma concl =
  IntTbl.add tacst_goalM cid (pp2str (pr_goal_concl_style_env env sigma concl))
(* NOTE(deh): No print because it's in shareM *)
let dump_pretty_tacst_goalM () = 
  IntTbl.iter (fun k v -> ml4tp_write (Printf.sprintf "%d: %s\n" k v)) tacst_goalM
*)

(* ************************************************************************** *)
(* Context printing *)

(* Note(deh): 
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
  (* GenSym.reset gs_ctxid; *)
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
 * 1. [constr_expr] is what the user writes
 * 2. [glob_constr] is desugared, but without types (i.e., no inference).
 * 3. [constr] is Coq kernel representation of Gallina terms
 *)

let rec show_global_reference gr =
  match gr with
  | VarRef v -> show_id v
  | ConstRef v -> Names.Constant.to_string v
  | IndRef (mi, i) -> Printf.sprintf "%s, %d" (Names.MutInd.to_string mi) i
  | ConstructRef ((mi, i), j) -> Printf.sprintf "%s, %d, %d" (Names.MutInd.to_string mi) i j

let show_cast_type show ct = 
  match ct with
  | CastConv a -> Printf.sprintf "C(%s)" (show a)
  | CastVM a -> Printf.sprintf "M(%s)" (show a)
  | CastCoerce -> Printf.sprintf "V()"
  | CastNative a -> Printf.sprintf "N(%s)" (show a)

let show_sort_info si =
  show_ls (fun (loc, s) -> s) ", " si

let show_glob_sort gs =
  match gs with
  | GProp -> "P"
  | GSet -> "S"
  | GType si -> Printf.sprintf "T(%s)" (show_sort_info si) 


let rec show_intro_pattern_expr show ipe =
  match ipe with
  | IntroForthcoming b -> Printf.sprintf "F(%b)" b
  | IntroNaming ipne -> Printf.sprintf "N(%s)" (show_intro_pattern_naming_expr ipne)
  | IntroAction ipae -> Printf.sprintf "A(%s)" (show_intro_pattern_action_expr show ipae)
and show_intro_pattern_naming_expr ipne =
  match ipne with
  | IntroIdentifier id -> Printf.sprintf "I(%s)" (show_id id)
  | IntroFresh id -> Printf.sprintf "F(%s)" (show_id id)
  | IntroAnonymous -> "A"
and show_intro_pattern_action_expr show ipae =
  match ipae with
  | IntroWildcard -> "W"
  | IntroOrAndPattern oaipe -> Printf.sprintf "O(%s)" (show_or_and_intro_pattern_expr show oaipe)
  | IntroInjection ls -> Printf.sprintf "I(%s)" (brackets (show_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ", " ls))
  | IntroApplyOn (a, (loc, ipe)) -> Printf.sprintf "A(%s, %s)" (show a) (show_intro_pattern_expr show ipe)
  | IntroRewrite b -> Printf.sprintf "R(%b)" b
and show_or_and_intro_pattern_expr show oaipe = 
  match oaipe with
  | IntroOrPattern ls ->
      brackets (show_ls (fun ls' -> brackets (show_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ", " ls')) ", " ls)
  | IntroAndPattern ls -> brackets (show_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ", " ls)

let rec show_cases_pattern cp =
  match cp with
  | PatVar (loc, n) -> show_name n
  | PatCstr (loc, ((mutind, i), j), cps, n) -> Printf.sprintf "(%s, %d, %d, %s, %s)" (Names.MutInd.to_string mutind) i j (brackets (show_ls show_cases_pattern ", " cps)) (show_name n)

let rec show_glob_constr gc =
  match gc with
  | GRef (l, gr, _) ->
      Printf.sprintf "!(%s)" (show_global_reference gr)
  | GVar (l, id) ->
      Printf.sprintf "V(%s)" (show_id id)
  | GEvar (l, en, args) -> 
      let f (id, gc) = Printf.sprintf "(%s, %s)" (show_id id) (show_glob_constr gc) in
      Printf.sprintf "E(%s, %s)" (show_id en) (brackets (show_ls f ", " args))
  | GPatVar (l, (b, pv)) ->
      Printf.sprintf "PV(%b, %s)" b (show_id pv)
  | GApp (l, gc, gcs) ->
      Printf.sprintf "A(%s, %s)" (show_glob_constr gc) (show_glob_constrs gcs)
  | GLambda (l, n, bk, gc1, gc2) ->
      Printf.sprintf "L(%s, %s, %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
  | GProd (l, n, bk, gc1, gc2) ->
      Printf.sprintf "P(%s, %s, %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
  | GLetIn (l, n, gc1, gc2) ->
      Printf.sprintf "LI(%s, %s, %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
  | GCases (l, cs, m_gc, tups, ccs) ->
      Printf.sprintf "C(%s, %s, %s, %s)" "TODO" (show_maybe show_glob_constr m_gc) (show_tomatch_tuples tups) (show_case_clauses ccs)
  | GLetTuple (l, ns, arg, gc1, gc2) ->
      let f (name, m_gc) = Printf.sprintf "(%s, %s)" (show_name name) (show_maybe show_glob_constr m_gc) in
      Printf.sprintf "LT(%s, %s, %s, %s)" (show_ls show_name ", " ns) (f arg) (show_glob_constr gc1) (show_glob_constr gc2)
  | GIf (l, gc, (n, m_gc), gc2, gc3) ->
      Printf.sprintf "I(%s, %s, %s)" (show_glob_constr gc) (show_glob_constr gc2) (show_glob_constr gc3)
  | GRec (l, fk, ids, gdss, gcs1, gcs2) ->
      Printf.sprintf "R(%s, %s, %s, %s, %s)" "TODO" (brackets (show_arr show_id ", " ids)) "TODO" (show_glob_constr_arr gcs1) (show_glob_constr_arr gcs2)
  | GSort (l, gsort) ->
      Printf.sprintf "S(%s)" (show_glob_sort gsort)
  | GHole (l, k, ipne, m_gga) ->
      Printf.sprintf "H(%s, %s, %s)" "TODO" (show_intro_pattern_naming_expr ipne) "TODO"
  | GCast (l, gc, gc_ty) ->
      Printf.sprintf "T(%s, %s)" (show_glob_constr gc) (show_cast_type show_glob_constr gc_ty)
and show_glob_constrs gcs =
  brackets (show_ls show_glob_constr ", " gcs)
and show_glob_constr_arr gcs =
  brackets (show_arr show_glob_constr ", " gcs)

and show_predicate_pattern (n, m_args) =
  let f (loc, (mutind, i), ns) = Printf.sprintf "(%s, %d, %s)" (Names.MutInd.to_string mutind) i (brackets (show_ls show_name ", " ns)) in
  Printf.sprintf "(%s, %s)" (show_name n) (show_maybe f m_args)
and show_tomatch_tuple (gc, pp) =
  Printf.sprintf "(%s, %s)" (show_glob_constr gc) (show_predicate_pattern pp)
and show_tomatch_tuples tmts =
  brackets (show_ls show_tomatch_tuple ", " tmts)

and show_case_clause (loc, ids, cps, gc) = 
  Printf.sprintf "(%s, %s, %s)" (brackets (show_ls show_id ", " ids)) (brackets (show_ls show_cases_pattern ", " cps)) (show_glob_constr gc)
and show_case_clauses ccs =
  brackets (show_ls show_case_clause ", " ccs)

(* ************************************************************************** *)
(* Ltac printing *)

(* Note(deh): 
 * A global term is a pair of
 * 1. a [glob_constr]
 * 2. an optional [constr_expr] that the glob_constr came from
 *)
let show_gtrm (gc, m_c) = show_glob_constr gc

let rec show_ltac_constant lc =
  Names.KerName.to_string lc
and show_g_reference gref =
  show_or_var (fun (loc, lc) -> show_ltac_constant lc) gref

(*
let show_red_Expr_gen show_a show_b show_c reg =
  match reg with
  | Red b -> Printf.sprintf "Red(%b)" b
  | Hnf -> "Hnf"
  | Simpl _ -> ""
*)

let show_may_eval mev =
  match mev with
  | ConstrEval (r, c) -> Printf.sprintf "E(%s, %s)" "TODO" (show_gtrm c)
  | ConstrContext ((_, id), c) -> Printf.sprintf "C(%s, %s)" (show_id id) (show_gtrm c)
  | ConstrTypeOf c -> Printf.sprintf "T(%s)" (show_gtrm c)
  | ConstrTerm c -> Printf.sprintf "M(%s)" (show_gtrm c)

let show_multi m =
  match m with
  | Precisely i -> Printf.sprintf "P(%d)" i
  | UpTo i -> Printf.sprintf "U(%d)" i
  | RepeatStar -> "*"
  | RepeatPlus -> "+"


let rec show_occurrences_gen f og =
  match og with
  | AllOccurrences -> "A"
  | AllOccurrencesBut ls -> Printf.sprintf "B(%s)" (brackets (show_ls f ", " ls))
  | NoOccurrences -> "N"
  | OnlyOccurrences ls -> Printf.sprintf "O(%s)" (brackets (show_ls f ", " ls))
and show_occurrences_expr oe =
  show_occurrences_gen (show_or_var string_of_int) oe
and show_with_occurrences show (oe, a) =
  Printf.sprintf "(%s, %s)" (show_occurrences_expr oe) (show a)


let rec show_hyp_location_flag hlf =
  match hlf with
  | InHyp -> "H"
  | InHypTypeOnly -> "T"
  | InHypValueOnly -> "V"
and show_hyp_location_expr ((occs, gnm), hlf) =
  Printf.sprintf "((%s, %s), %s)" (show_occurrences_expr occs) (show_gname gnm) (show_hyp_location_flag hlf)
and show_clause_expr ce = 
  Printf.sprintf "(%s, %s)" (show_maybe (fun x -> show_ls show_hyp_location_expr ", " x) ce.onhyps) (show_occurrences_expr ce.concl_occs)


let rec show_quantified_hypothesis qhyp = 
  match qhyp with
  | AnonHyp i -> Printf.sprintf "@%d" i
  | NamedHyp id -> show_id id
and show_explicit_binding' show_a (loc, qhyp, a) =
  Printf.sprintf "(%s, %s)" (show_quantified_hypothesis qhyp) (show_a a)
and show_bindings show_a b =
  match b with
  | ImplicitBindings ls ->
      Printf.sprintf "I(%s)" (brackets (show_ls show_a ", " ls))
  | ExplicitBindings ebs ->
      Printf.sprintf "E(%s)" (brackets (show_ls (show_explicit_binding' show_a) ", " ebs))
  | NoBindings -> "N"
and show_with_bindings show_a (a, b) = 
  Printf.sprintf "(%s, %s)" (show_a a) (show_bindings show_a b)
and show_with_bindings_arg show_a (cf, b) =
  Printf.sprintf "(%s, %s)" (show_maybe string_of_bool cf) (show_with_bindings show_a b)


let rec show_destruction_arg show_a (cf, cda) =
  Printf.sprintf "(%s, %s)" (show_maybe string_of_bool cf) (show_core_destruction_arg show_a cda)
and show_core_destruction_arg show_a cda =
  match cda with
  | ElimOnConstr a -> Printf.sprintf "C(%s)" (show_a a)
  | ElimOnIdent (loc, id) -> Printf.sprintf "I(%s)" (show_id id)
  | ElimOnAnonHyp i -> Printf.sprintf "A(%d)" i


let rec show_induction_clause (wbs_da, (ml_ipne, movl_oaipe), m_ce) =
  let f (loc, ipne) = show_intro_pattern_naming_expr ipne in
  let g (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
  let g' = show_maybe (show_or_var g) in
  Printf.sprintf "(%s, %s, %s, %s)" (show_destruction_arg (show_with_bindings show_gtrm) wbs_da) (show_maybe f ml_ipne) (g' movl_oaipe) (show_maybe show_clause_expr m_ce)
and show_induction_clause_list (ics, m_bs) =
  Printf.sprintf "(%s, %s)" (brackets (show_ls show_induction_clause ", " ics)) (show_maybe (show_with_bindings show_gtrm) m_bs)


let rec show_inversion_strength is =
  match is with
  | NonDepInversion (ik, gnms, movl_oaipe) ->
      let f (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
      let g = show_or_var f in
      Printf.sprintf "NonDep(%s, %s, %s)" (show_inversion_kind ik) (brackets (show_ls show_gname ", " gnms)) (show_maybe g movl_oaipe)
  | DepInversion (ik, maybe_c, movl_oaipe) ->
      let f (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
      let g = show_or_var f in
      Printf.sprintf "Dep(%s, %s, %s)" (show_inversion_kind ik) (show_maybe show_gtrm maybe_c) ((show_maybe g movl_oaipe))
  | InversionUsing (c, gnms) ->
      Printf.sprintf "Using(%s, %s)" (show_gtrm c) (brackets (show_ls show_gname ", " gnms))
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
  | MsgString s -> s
  | MsgInt i -> string_of_int i
  | MsgIdent gnm -> show_gname gnm

let show_goal_selector gs =
  match gs with
  | SelectNth i -> string_of_int i
  | SelectList ls -> show_ls (fun (i, j) -> Printf.sprintf "(%d, %d)" i j) ", " ls
  | SelectId id -> Id.to_string id
  | SelectAll -> "A"


let rec show_match_rule show_pat show_tac mrule =
  match mrule with
  | Pat (hyps, pat, tac) -> Printf.sprintf "Pat(%s, %s, %s)" (brackets (show_ls (show_match_context_hyps show_pat) ", " hyps)) (show_match_pattern show_pat pat) (show_tac tac)
  | All tac -> Printf.sprintf "All(%s)" (show_tac tac)
and show_match_rules show_pat show_tac mrules =
  brackets (show_ls (show_match_rule show_pat show_tac) ", " mrules)
and show_match_pattern show_pat mp =
  match mp with
  | Term p -> show_pat p
  | Subterm (b, maybe_id, p) -> Printf.sprintf "%b %s %s" b (show_maybe show_id maybe_id) (show_pat p)
and show_match_context_hyps show_pat hyps =
  match hyps with
  | Hyp ((loc, name), mp) -> Printf.sprintf "Hyp(%s, %s)" (show_name name) (show_match_pattern show_pat mp)
  | Def ((loc, name), mp1, mp2) -> Printf.sprintf "Def(%s, %s, %s)" (show_name name) (show_match_pattern show_pat mp1) (show_match_pattern show_pat mp2)

let show_ml_tactic_entry mlen =
  let name = mlen.mltac_name in
  Printf.sprintf "(%s, %s, %d)" name.mltac_plugin name.mltac_tactic mlen.mltac_index

(*
let show_generic_arg show ga =
  match ga with
  | GenArg (Glbwit wit, x) ->
    match wit with
    | ListArg wit -> show wit
    | OptArg wit -> show wit
    | PairArg (wit1, wit2) -> Printf.sprintf "(%s, %s)" (show wit1) (show wit2)
    | ExtraArg s -> ArgT.repr s
*)

let rec show_tactic_arg ta =
  match ta with
  | TacGeneric ga -> "Generic(TODO)" (* Printf.sprintf "Generic(%s)" (show_generic_arg (fun _ -> "") ga) *)
  | ConstrMayEval mev -> show_may_eval mev
  | Reference r -> Printf.sprintf "Reference(%s)" (show_g_reference r)
  | TacCall (loc, r, targs) -> Printf.sprintf "Call(%s, %s)" (show_g_reference r) (show_tactic_args targs)
  | TacFreshId sovs -> Printf.sprintf "FreshId(%s)" (brackets (show_ls (fun x -> show_or_var (fun x -> x) x) ", " sovs))
  | Tacexp tac -> Printf.sprintf "Exp(%s)" (show_tac tac)
  | TacPretype c -> Printf.sprintf "Pretype(%s)" (show_gtrm c)
  | TacNumgoals -> "Numgoals"
and show_tactic_args tas = 
  brackets (show_ls show_tactic_arg ", " tas)

and show_atomic_tac atac =
  match atac with
  | TacIntroPattern (ef, ipes) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      Printf.sprintf "IntroPattern(%b, %s)" ef (show_ls f ", " ipes)
  | TacApply (af, ef, bargss, gnm_and_ipe) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      let g (gnm, x) = Printf.sprintf "(%s, %s)" (show_gname gnm) (show_maybe f x) in
      Printf.sprintf "Apply(%b, %b, %s, %s)" af ef (brackets (show_ls (show_with_bindings_arg show_gtrm) ", " bargss)) (show_maybe g gnm_and_ipe)
  | TacElim (ef, bargs, maybe_wb) ->
      Printf.sprintf "Elim(%b, %s, %s)" ef (show_with_bindings_arg show_gtrm bargs) (show_maybe (show_with_bindings show_gtrm) maybe_wb)
  | TacCase (ef, bargs) ->
      Printf.sprintf "Case(%b, %s)" ef (show_with_bindings_arg show_gtrm bargs)
  | TacMutualFix (id, i, body) ->
      let f (id, i, c) = Printf.sprintf "(%s, %d, %s)" (show_id id) i (show_gtrm c) in
      Printf.sprintf "MutualFix(%s, %d, %s)" (show_id id) i (brackets (show_ls f ", " body))
  | TacMutualCofix (id, body) ->
      let f (id, c) = Printf.sprintf "(%s, %s)" (show_id id) (show_gtrm c) in
      Printf.sprintf "MutualCofix(%s,  %s)" (show_id id) (brackets (show_ls f ", " body))
  | TacAssert (b, mm_tac, ml_ipe, c) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      let g = show_maybe f in
      Printf.sprintf "Assert(%b, %s, %s, %s)" b (show_maybe (show_maybe show_tac) mm_tac) (g ml_ipe) (show_gtrm c)
  | TacGeneralize ls ->
      let f (wo, name) = Printf.sprintf "(%s, %s)" (show_with_occurrences show_gtrm wo) (show_name name) in
      Printf.sprintf "Generalize(%s)" (brackets (show_ls f ", " ls))
  | TacLetTac (name, c, ce, lf, ml_ipe) ->
      let f (loc, ipne) = show_intro_pattern_naming_expr ipne in
      Printf.sprintf "LetTac(%s, %s, %s, %b, %s)" (show_name name) (show_gtrm c) (show_clause_expr ce) lf (show_maybe f ml_ipe)
  | TacInductionDestruct (rf, ef, ics) ->
      Printf.sprintf "InductionDestruct(%b, %b, %s)" rf ef (show_induction_clause_list ics)
  | TacReduce (reg, ce) ->
      Printf.sprintf "Reduce(%s, %s)" "TODO" (show_clause_expr ce)
  | TacChange (maybe_pat, dtrm, ce) ->
      let f (_, gtrm, cpat) = show_gtrm gtrm in
      Printf.sprintf "MutualFix(%s, %s, %s)" (show_maybe f maybe_pat) (show_gtrm dtrm) (show_clause_expr ce)
  | TacRewrite (ef, rargs, ce, maybe_tac) ->
      let f (b, m, barg) = Printf.sprintf "(%b, %s, %s)" b (show_multi m) (show_with_bindings_arg show_gtrm barg) in
      Printf.sprintf "Rewrite(%b, %s, %s, %s)" ef (brackets (show_ls f ", " rargs)) (show_clause_expr ce) (show_maybe show_tac maybe_tac)
  | TacInversion (is, qhyp) -> Printf.sprintf "Inversion(%s, %s)" (show_inversion_strength is) (show_quantified_hypothesis qhyp)

and show_tac tac =
  match tac with
  | TacAtom (loc, atac) ->
      show_atomic_tac atac
  | TacThen (tac1, tac2) ->
      Printf.sprintf "Then(%s, %s)" (show_tac tac1) (show_tac tac2)
  | TacDispatch tacs ->
      Printf.sprintf "Dispatch(%s)" (show_tacs tacs)
  | TacExtendTac (tacs1, tac, tacs2) ->
      Printf.sprintf "ExtendTac(%s, %s, %s)" (show_tac_arr tacs1) (show_tac tac) (show_tac_arr tacs2)
  | TacThens (tac, tacs) ->
      Printf.sprintf "Thens(%s, %s)" (show_tac tac) (show_tacs tacs)
  | TacThens3parts (tac1, tac1s, tac2, tac2s) ->
      Printf.sprintf "Thens3parts(%s, %s, %s, %s)" (show_tac tac1) (show_tac_arr tac1s) (show_tac tac2) (show_tac_arr tac2s)
  | TacFirst tacs ->
      Printf.sprintf "First(%s)" (show_tacs tacs)
  | TacComplete tac ->
      Printf.sprintf "Complete(%s)" (show_tac tac)
  | TacSolve tacs ->
      Printf.sprintf "Solve(%s)" (show_tacs tacs)
  | TacTry tac ->
      Printf.sprintf "Try(%s)" (show_tac tac)
  | TacOr (tac1, tac2) ->
      Printf.sprintf "Or(%s, %s)" (show_tac tac1) (show_tac tac2)
  | TacOnce tac ->
      Printf.sprintf "Once(%s)" (show_tac tac)
  | TacExactlyOnce tac ->
      Printf.sprintf "ExactlyOnce(%s)" (show_tac tac)
  | TacIfThenCatch (tac1, tac2, tac3) ->
      Printf.sprintf "IfThenCatch(%s, %s, %s)" (show_tac tac1) (show_tac tac2) (show_tac tac3)
  | TacOrelse (tac1, tac2) ->
      Printf.sprintf "Orelse(%s, %s)" (show_tac tac1) (show_tac tac2)
  | TacDo (iov, tac) ->
      Printf.sprintf "Do(%s, %s)" (show_or_var string_of_int iov) (show_tac tac)
  | TacTimeout (iov, tac) ->
      Printf.sprintf "Timeout(%s, %s)" (show_or_var string_of_int iov) (show_tac tac)
  | TacTime (maybe_str, tac) ->
      Printf.sprintf "Time(%s, %s)" (show_maybe (fun x -> x) maybe_str) (show_tac tac)
  | TacRepeat tac ->
      Printf.sprintf "Repeat(%s)" (show_tac tac)
  | TacProgress tac ->
      Printf.sprintf "Progress(%s)" (show_tac tac)
  | TacShowHyps tac ->
      Printf.sprintf "ShowHyps(%s)" (show_tac tac)
  | TacAbstract (tac, maybe_id) ->
      Printf.sprintf "Asbtract(%s, %s)" (show_tac tac) (show_maybe show_id maybe_id)
  | TacId msgs ->
      Printf.sprintf "Id(%s)" (brackets (show_ls show_message_token ", " msgs))
  | TacFail (gf, iov, msgs) ->
      Printf.sprintf "Info(%s, %s, %s)" (show_global_flag gf) (show_or_var string_of_int iov) (brackets (show_ls show_message_token ", " msgs))
  | TacInfo tac ->
      Printf.sprintf "Info(%s)" (show_tac tac)
  | TacLetIn (rf, bindings, tac) ->
      let f ((loc, id), targ) = Printf.sprintf "(%s, %s)" (show_id id) (show_tactic_arg targ) in
      Printf.sprintf "Let(%b, %s, %s)" rf (brackets (show_ls f ", " bindings)) (show_tac tac)
  | TacMatch (lf, tac, mrules) ->
      (* TODO *)
      let f (_, gtrm, cpat) = show_gtrm gtrm in
      Printf.sprintf "Match(%s, %s, %s)" (show_lazy_flag lf) (show_tac tac) (show_match_rules f show_tac mrules)
  | TacMatchGoal (lf, df, mrules) ->
      (* TODO *)
      let f (_, gtrm, cpat) = show_gtrm gtrm in
      Printf.sprintf "MatchGoal(%s, %b, %s)" (show_lazy_flag lf) df (show_match_rules f show_tac mrules)
  | TacFun (maybe_ids, tac) ->
      Printf.sprintf "Fun(%s, %s)" (brackets (show_ls (show_maybe show_id) ", " maybe_ids)) (show_tac tac)
  | TacArg (loc, targ) ->
      Printf.sprintf "Arg(%s)" (show_tactic_arg targ)
  | TacSelect (gs, tac) ->
      Printf.sprintf "Select(%s, %s)" (show_goal_selector gs) (show_tac tac)
  | TacML (loc, mlen, targs) ->
      Printf.sprintf "ML(%s, %s)" (show_ml_tactic_entry mlen) (show_tactic_args targs)
  | TacAlias (loc, kername, targs) ->
      Printf.sprintf "Alias(%s, %s)" (KerName.to_string kername) (show_tactic_args targs)
and show_tacs tacs =
  brackets (show_ls show_tac ", " tacs)
and show_tac_arr tacs = 
  brackets (show_arr show_tac ", " tacs)



(* ************************************************************************** *)
(* Junk *)

(*
let rec show_targ targ =
  match targ with
  | TacGeneric _ -> Printf.sprintf "Generic(%s)" "TODO"
  | ConstrMayEval mev -> show_may_eval mev
  | Reference r -> Printf.sprintf "Reference(%s)" (show_g_reference r)
  | TacCall (loc, r, targs) -> Printf.sprintf "Call(%s, %s)" (show_g_reference r) (show_targs targs)
  | TacFreshId sovs -> Printf.sprintf "FreshId(%s)" (brackets (show_ls (fun x -> show_or_var (fun x -> x) x) ", " sovs))
  | Tacexp tac -> Printf.sprintf "Exp(%s)" (show_tac tac)
  | TacPretype c -> Printf.sprintf "Pretype(%s)" (show_gtrm c)
  | TacNumgoals -> "Numgoals"
and show_targs targs = 
  brackets (show_ls show_targ ", " targs)
and show_atac atac =
  match atac with
  | TacIntroPattern (ef, ipes) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      Printf.sprintf "IntroPattern(%b, %s)" ef (show_ls f ", " ipes)
  | TacApply (af, ef, bargss, gnm_and_ipe) ->
      let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
      let g (gnm, x) = Printf.sprintf "(%s, %s)" (show_gname gnm) (show_maybe f x) in
      Printf.sprintf "Apply(%b, %b, %s, %s)" af ef (brackets (show_ls (show_with_bindings_arg show_gtrm) ", " bargss)) (show_maybe g gnm_and_ipe)
  | TacElim (ef, bargs, maybe_wb) -> Printf.sprintf "Elim(%b, %s, %s)" ef (show_with_bindings_arg show_gtrm bargs) (show_maybe (show_with_bindings show_gtrm) maybe_wb)
  | TacCase (ef, bargs) -> Printf.sprintf "Case(%b, %s)" ef (show_with_bindings_arg show_gtrm bargs)
  | TacMutualFix (id, i, body) ->
      let f (id, i, c) = Printf.sprintf "(%s, %d, %s)" (show_id id) i (show_gtrm c) in
      Printf.sprintf "MutualFix(%s, %d, %s)" (show_id id) i (brackets (show_ls f ", " body))
  | TacMutualCofix (id, body) ->
      let f (id, c) = Printf.sprintf "(%s, %s)" (show_id id) (show_gtrm c) in
      Printf.sprintf "MutualCofix(%s,  %s)" (show_id id) (brackets (show_ls f ", " body))
  | TacAssert (b, mm_tac, ml_ipe, c) ->
      Printf.sprintf "Assert(%b, %s, %s, %s)" b (show_maybe (show_maybe show_tac) mm_tac) (show_maybe_located_intro_pattern_naming_expr ml_ipe) (show_gtrm c)
  | TacGeneralize ls ->
      let f (wo, name) = Printf.sprintf "(%s, %s)" (show_with_occurrences show_gtrm wo) (show_name name) in
      Printf.sprintf "Generalize(%s)" (brackets (show_ls f ", " ls))
  | TacLetTac (name, c, ce, lf, ml_ipe) ->
      let f (loc, ipne) = show_intro_pattern_naming_expr ipne in
      Printf.sprintf "LetTac(%s, %s, %s, %b, %s)" (show_name name) (show_gtrm c) (show_clause_expr ce) lf (show_maybe f ml_ipe)
  | TacInductionDestruct (rf, ef, ics) -> Printf.sprintf "InductionDestruct(%b, %b, %s)" rf ef (show_induction_clause_list ics)
  | TacReduce (reg, ce) -> Printf.sprintf "Reduce(%s, %s)" "TODO" (show_clause_expr ce)
  | TacChange (maybe_pat, dtrm, ce) -> Printf.sprintf "MutualFix(%s, %s, %s)" "TODO" (show_gtrm dtrm) (show_clause_expr ce)
  | TacRewrite (ef, rargs, ce, maybe_tac) -> Printf.sprintf "Rewrite(%b, %s, %s, %s)" ef (brackets (show_ls show_rewrite_arg ", " rargs)) (show_clause_expr ce) (show_maybe show_tac maybe_tac)
  | TacInversion (is, qhyp) -> Printf.sprintf "Inversion(%s, %s)" (show_inversion_strength is) (show_quantified_hypothesis qhyp)
and show_induction_clause (wbs_da, (ml_ipne, movl_oaipe), m_ce) =
  let f (loc, ipne) = show_intro_pattern_naming_expr ipne in
  let g (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
  let g' = show_maybe (show_or_var g) in
  Printf.sprintf "(%s, %s, %s, %s)" (show_destruction_arg (show_with_bindings show_gtrm) wbs_da) (show_maybe f ml_ipne) (g' movl_oaipe) (show_maybe show_clause_expr m_ce)
and show_induction_clause_list (ics, m_bs) =
  Printf.sprintf "(%s, %s)" (brackets (show_ls show_induction_clause ", " ics)) (show_maybe (show_with_bindings show_gtrm) m_bs)
and show_destruction_arg show_a (cf, cda) =
  Printf.sprintf "(%s, %s)" (show_maybe string_of_bool cf) (show_core_destruction_arg show_a cda)
and show_core_destruction_arg show_a cda =
  match cda with
  | ElimOnConstr a -> Printf.sprintf "C(%s)" (show_a a)
  | ElimOnIdent (loc, id) -> Printf.sprintf "I(%s)" (show_id id)
  | ElimOnAnonHyp i -> Printf.sprintf "A(%d)" i
and show_maybe_located_intro_pattern_naming_expr ml_ipe =
  let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
  show_maybe f ml_ipe
and show_multi m =
  match m with
  | Precisely i -> Printf.sprintf "P(%d)" i
  | UpTo i -> Printf.sprintf "U(%d)" i
  | RepeatStar -> "*"
  | RepeatPlus -> "+"
and show_rewrite_arg (b, m, barg) =
  Printf.sprintf "(%b, %s, %s)" b (show_multi m) (show_with_bindings_arg show_gtrm barg)
and show_ltac_constant lc =
  Names.KerName.to_string lc
and show_g_reference gref =
  show_or_var (fun (loc, lc) -> show_ltac_constant lc) gref
and show_occurrences_gen f og =
  match og with
  | AllOccurrences -> "A"
  | AllOccurrencesBut ls -> Printf.sprintf "B(%s)" (brackets (show_ls f ", " ls))
  | NoOccurrences -> "N"
  | OnlyOccurrences ls -> Printf.sprintf "O(%s)" (brackets (show_ls f ", " ls))
and show_occurrences_expr oe =
  show_occurrences_gen show_int_or_var oe
and show_with_occurrences show_a (oe, a) =
  Printf.sprintf "(%s, %s)" (show_occurrences_expr oe) (show_a a)
and show_hyp_location_flag hlf =
  match hlf with
  | InHyp -> "H"
  | InHypTypeOnly -> "T"
  | InHypValueOnly -> "V"
and show_hyp_location_expr ((occs, gnm), hlf) =
  Printf.sprintf "((%s, %s), %s)" (show_occurrences_expr occs) (show_gname gnm) (show_hyp_location_flag hlf)
and show_clause_expr ce = 
  Printf.sprintf "(%s, %s)" (show_maybe (fun x -> show_ls show_hyp_location_expr ", " x) ce.onhyps) (show_occurrences_expr ce.concl_occs)
and show_inversion_kind ik = 
  match ik with
  | SimpleInversion -> "S"
  | FullInversion -> "F"
  | FullInversionClear -> "FC"
and show_inversion_strength is =
  match is with
  | NonDepInversion (ik, gnms, movl_oaipe) ->
      let f (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
      let g = show_or_var f in
      Printf.sprintf "NonDep(%s, %s, %s)" (show_inversion_kind ik) (brackets (show_ls show_gname ", " gnms)) (show_maybe g movl_oaipe)
  | DepInversion (ik, maybe_c, movl_oaipe) ->
      let f (loc, oaipe) = show_or_and_intro_pattern_expr show_gtrm oaipe in
      let g = show_or_var f in
      Printf.sprintf "Dep(%s, %s, %s)" (show_inversion_kind ik) (show_maybe show_gtrm maybe_c) ((show_maybe g movl_oaipe))
  | InversionUsing (c, gnms) -> Printf.sprintf "Using(%s, %s)" (show_gtrm c) (brackets (show_ls show_gname ", " gnms))
and show_tac tac : string =
  match tac with
  | TacAtom (loc, atac) -> show_atac atac
  | TacThen (tac1, tac2) -> Printf.sprintf "Then(%s, %s)" (show_tac tac1) (show_tac tac2)
  | TacDispatch tacs -> Printf.sprintf "Dispatch(%s)" (show_tacs tacs)
  | TacExtendTac (tacs1, tac, tacs2) -> Printf.sprintf "ExtendTac(%s, %s, %s)" (show_tac_arr tacs1) (show_tac tac) (show_tac_arr tacs2)
  | TacThens (tac, tacs) -> Printf.sprintf "Thens(%s, %s)" (show_tac tac) (show_tacs tacs)
  | TacThens3parts (tac1, tac1s, tac2, tac2s) -> Printf.sprintf "Thens3parts(%s, %s, %s, %s)" (show_tac tac1) (show_tac_arr tac1s) (show_tac tac2) (show_tac_arr tac2s)
  | TacFirst tacs -> Printf.sprintf "First(%s)" (show_tacs tacs)
  | TacComplete tac -> Printf.sprintf "Complete(%s)" (show_tac tac)
  | TacSolve tacs -> Printf.sprintf "Solve(%s)" (show_tacs tacs)
  | TacTry tac -> Printf.sprintf "Try(%s)" (show_tac tac)
  | TacOr (tac1, tac2) -> Printf.sprintf "Or(%s, %s)" (show_tac tac1) (show_tac tac2)
  | TacOnce tac -> Printf.sprintf "Once(%s)" (show_tac tac)
  | TacExactlyOnce tac -> Printf.sprintf "ExactlyOnce(%s)" (show_tac tac)
  | TacIfThenCatch (tac1, tac2, tac3) -> Printf.sprintf "IfThenCatch(%s, %s, %s)" (show_tac tac1) (show_tac tac2) (show_tac tac3)
  | TacOrelse (tac1, tac2) -> Printf.sprintf "Orelse(%s, %s)" (show_tac tac1) (show_tac tac2)
  | TacDo (iov, tac) -> Printf.sprintf "Do(%s, %s)" (show_int_or_var iov) (show_tac tac)
  | TacTimeout (iov, tac) -> Printf.sprintf "Timeout(%s, %s)" (show_int_or_var iov) (show_tac tac)
  | TacTime (maybe_str, tac) -> Printf.sprintf "Time(%s, %s)" (show_maybe (fun x -> x) maybe_str) (show_tac tac)
  | TacRepeat tac -> Printf.sprintf "Repeat(%s)" (show_tac tac)
  | TacProgress tac -> Printf.sprintf "Progress(%s)" (show_tac tac)
  | TacShowHyps tac -> Printf.sprintf "ShowHyps(%s)" (show_tac tac)
  | TacAbstract (tac, maybe_id) -> Printf.sprintf "Do(%s, %s)" (show_tac tac) (show_maybe show_id maybe_id)
  | TacId msgs -> Printf.sprintf "Id(%s)" (brackets (show_ls show_message_token ", " msgs))
  | TacFail (gf, iov, msgs) -> Printf.sprintf "Info(%s, %s, %s)" (show_global_flag gf) (show_int_or_var iov) (brackets (show_ls show_message_token ", " msgs))
  | TacInfo tac -> Printf.sprintf "Info(%s)" (show_tac tac)
  | TacLetIn (rf, bindings, tac) ->
      let f ((loc, id), targ) = Printf.sprintf "(%s, %s)" (show_id id) (show_targ targ) in
      Printf.sprintf "Let(%b, %s, %s)" rf (brackets (show_ls f ", " bindings)) (show_tac tac)
  | TacMatch (lf, tac, mrules) -> Printf.sprintf "Match(%s, %s, %s)" (show_lazy_flag lf) (show_tac tac) (show_match_rules mrules)
  | TacMatchGoal (lf, df, mrules) -> Printf.sprintf "MatchGoal(%s, %b, %s)" (show_lazy_flag lf) df (show_match_rules mrules)
  | TacFun (maybe_ids, tac) -> Printf.sprintf "Fun(%s, %s)" (brackets (show_ls (show_maybe show_id) ", " maybe_ids)) (show_tac tac)
  | TacArg (loc, targ) -> Printf.sprintf "Arg(%s)" (show_targ targ)
  | TacSelect (gs, tac) -> Printf.sprintf "Select(%s, %s)" (show_goal_selector gs) (show_tac tac)
  | TacML (loc, mlen, targs) -> Printf.sprintf "ML(%s, %s)" (show_ml_tactic_entry mlen) (show_targs targs)
  | TacAlias (loc, kername, targs) -> Printf.sprintf "Alias(%s, %s)" (KerName.to_string kername) (show_targs targs)
and show_tacs tacs =
  brackets (show_ls show_tac ", " tacs)
and show_tac_arr tacs = 
  brackets (show_arr show_tac ", " tacs)
and show_match_pattern pat =
  match pat with
  | Term c -> show_gtrm c
  | Subterm (b, maybe_id, c) -> Printf.sprintf "%b %s %s" b (show_maybe show_id maybe_id) (show_gtrm c)
and show_match_context_hyps hyps =
  match hyps with
  | Hyp ((loc, name), pat) -> Printf.sprintf "Hyp(%s, %s)" (show_name name) (show_match_pattern pat)
  | Def ((loc, name), pat1, pat2) -> Printf.sprintf "Def(%s, %s, %s)" (show_name name) (show_match_pattern pat1) (show_match_pattern pat2)
and show_match_rule mrule =
  match mrule with
  | Pat (hyps, pat, tac) -> Printf.sprintf "Pat(%s, %s, %s)" (brackets (show_ls show_match_context_hyps ", " hyps)) (show_match_pattern pat) (show_tac tac)
  | All tac -> Printf.sprintf "All(%s)" (show_tac tac)
and show_match_rules mrules =
  brackets (show_ls show_match_rule ", " mrules)
and show_int_or_var iov = 
  show_or_var string_of_int iov
and show_lazy_flag lf =
  match lf with
  | General -> "G"
  | Select -> "S"
  | Once -> "O"
and show_global_flag gf =
  match gf with
  | TacGlobal -> "G"
  | TacLocal -> "L"
and show_goal_selector gs =
  match gs with
  | SelectNth i -> string_of_int i
  | SelectList ls -> show_ls (fun (i, j) -> Printf.sprintf "(%d, %d)" i j) ", " ls
  | SelectId id -> Id.to_string id
  | SelectAll -> "A"
and show_message_token mtok = 
  match mtok with
  | MsgString s -> s
  | MsgInt i -> string_of_int i
  | MsgIdent gnm -> show_gname gnm
and show_ml_tactic_entry mlen =
  let name = mlen.mltac_name in
  Printf.sprintf "(%s, %s, %d)" name.mltac_plugin name.mltac_tactic mlen.mltac_index
*)

(*
let rec show_constr_expr ce =
  match ce with
  | CApp (loc, (pf, ce), args) ->
      let f (ce', _) = show_constr_expr ce' in
      Printf.sprintf "A(%s, %s)" (show_constr_expr ce) (brackets (show_ls f ", " args))
  | _ -> "FOO"

(* type glob_constr_and_expr = Glob_term.glob_constr * constr_expr option *)
let show_dtrm interp (dtrm: glob_constr_and_expr) = 
  let (gc, m_c) = dtrm in
  show_constr (interp gc)
  (* show_maybe (fun c -> show_gconstr (interp c)) m_c *)
*)



(*
let deh_show_vernac_expr ve =
  match ve with
  | VernacLoad (_, _) -> (* verbose_flag * string *) "VernacLoad(?, ?)"
  | VernacTime _ -> "VernacTime"
  | VernacRedirect _ -> "VernacRedirect"
  | VernacTimeout _ -> "VernacTimeout"
  | VernacFail _ -> "VernacFail"
  | VernacError _ -> "VernacError"

  | VernacSyntaxExtension _ -> "VernacSyntaxExtension"
  | VernacOpenCloseScope _ -> "VernacOpenCloseScope"
  | VernacDelimiters _ -> "VernacDelimiters"
  | VernacBindScope _ -> "VernacBindScope"
  | VernacInfix _ -> "VernacInfix"
  | VernacNotation _ -> "VernacNotation"
  | VernacNotationAddFormat _ -> "VernacNotationAddFormat"

  | VernacDefinition _ -> "VernacDefinition"
  | VernacStartTheoremProof _ -> "VernacStartTheoremProof"
  | VernacEndProof _ -> "VernacEndProof"
  | VernacExactProof _ -> "VernacExactProof"
  | VernacAssumption _ -> "VernacAssumption"
  | VernacInductive _ -> "VernacInductive"
  | VernacFixpoint _ -> "VernacFixpoint"
  | VernacCoFixpoint _ -> "VernacCoFixpoint"
  | VernacScheme _ -> "VernacScheme"
  | VernacCombinedScheme _ -> "VernacCombinedScheme"
  | VernacUniverse _ -> "VernacUniverse"
  | VernacConstraint _ -> "VernacConstraint"

  | VernacBeginSection _ -> "VernacBeginSection"
  | VernacEndSegment _ -> "VernacEndSegment"
  | VernacRequire _ -> "VernacRequire"
  | VernacImport _ -> "VernacImport"
  | VernacCanonical _ -> "VernacCanonical"
  | VernacCoercion _ -> "VernacCoercion"
  | VernacIdentityCoercion _ -> "VernacIdentityCoercion"
  | VernacNameSectionHypSet _ -> "VernacNameSectionHypSet"

  | VernacInstance _ -> "VernacInstance"
  | VernacContext _ -> "VernacContext"
  | VernacDeclareInstances _ -> "VernacDeclareInstances"
  | VernacDeclareClass _ -> "VernacDeclareClass"

  | VernacDeclareModule _ -> "VernacDeclareModule"
  | VernacDefineModule _ -> "VernacDefineModule"
  | VernacDeclareModuleType _ -> "VernacDeclareModuleType"
  | VernacInclude _ -> "VernacInclude"

  | VernacSolveExistential _ -> "VernacSolveExistential"

  | VernacAddLoadPath _ -> "VernacAddLoadPath"
  | VernacRemoveLoadPath _ -> "VernacRemoveLoadPath"
  | VernacAddMLPath _ -> "VernacAddMLPath"
  | VernacDeclareMLModule _ -> "VernacDeclareMLModule"
  | VernacChdir _ -> "VernacChdir"

  | VernacWriteState _ -> "VernacWriteState"
  | VernacRestoreState _ -> "VernacRestoreState"

  | VernacResetName _ -> "VernacResetName"
  | VernacResetInitial -> "VernacResetInitial"
  | VernacBack _ -> "VernacBack"
  | VernacBackTo _ -> "VernacBackTo"

  | VernacCreateHintDb _ -> "VernacCreateHintDb"
  | VernacRemoveHints _ -> "VernacRemoveHints"
  | VernacHints _ -> "VernacHints"
  | VernacSyntacticDefinition _ -> "VernacSyntacticDefinition"
  | VernacDeclareImplicits _ -> "VernacDeclareImplicits"
  | VernacArguments _ -> "VernacArguments"
  | VernacArgumentsScope _ -> "VernacArgumentsScope"
  | VernacReserve _ -> "VernacReserve"
  | VernacGeneralizable _ -> "VernacGeneralizable"
  | VernacSetOpacity _ -> "VernacSetOpacity"
  | VernacSetStrategy _ -> "VernacSetStrategy"
  | VernacUnsetOption _ -> "VernacUnsetOption"
  | VernacSetOption _ -> "VernacSetOption"
  | VernacSetAppendOption _ -> "VernacSetAppendOption"
  | VernacAddOption _ -> "VernacAddOption"
  | VernacRemoveOption _ -> "VernacRemoveOption"
  | VernacMemOption _ -> "VernacMemOption"
  | VernacPrintOption _ -> "VernacPrintOption"
  | VernacCheckMayEval _ -> "VernacCheckMayEval"
  | VernacGlobalCheck _ -> "VernacGlobalCheck"
  | VernacDeclareReduction _ -> "VernacDeclareReduction"
  | VernacPrint _ -> "VernacPrint"
  | VernacSearch _ -> "VernacSearch"
  | VernacLocate _ -> "VernacLocate"
  | VernacRegister _ -> "VernacRegister"
  | VernacComments _ -> "VernacComments"

  | VernacStm _ -> "VernacStm"

  | VernacGoal _ -> "VernacGoal"
  | VernacAbort _ -> "VernacAbort"
  | VernacAbortAll -> "VernacAbortAll"
  | VernacRestart -> "VernacRestart"
  | VernacUndo _ -> "VernacUndo"
  | VernacUndoTo _ -> "VernacUndoTo"
  | VernacBacktrack _ -> "VernacBacktrack"
  | VernacFocus _ -> "VernacFocus"
  | VernacUnfocus -> "VernacUnfocus"
  | VernacUnfocused -> "VernacUnfocused"
  | VernacBullet _ -> "VernacBullet"
  | VernacSubproof _ -> "VernacSubproof"
  | VernacEndSubproof -> "VernacEndSubproof"
  | VernacShow _ -> "VernacShow"
  | VernacCheckGuard -> "VernacCheckGuard"
  | VernacProof _ -> "VernacProof"
  | VernacProofMode _ -> "VernacProofMode"

  | VernacToplevelControl _ -> "VernacToplevelControl"

  | VernacExtend ((str, i), _) -> "VernacExtend(" ^ str ^ ", " ^ string_of_int i ^ ")"

  | VernacProgram _ -> "VernacProgram"
  | VernacPolymorphic _ -> "VernacPolymorphic"
  | VernacLocal _ -> "VernacLocal"
*)

(*
let rec deh_show_vernac_type vt =
  match vt with
  | VtStartProof (name, _, names) -> Printf.sprintf "VtStartProof(%s, %s)" name (deh_show_names names)
  | VtSideff (_) -> "VtSideff"
  | VtQed (_) -> "VtQed"
  | VtProofStep _ -> "VtProofStep"
  | VtProofMode (_) -> "VtProofMode"
  | VtQuery (_, _) -> "VtQuery"
  | VtStm (_, _) -> "VtStm"
  | VtUnknown -> "VtUnknown"
*)

(*
let constr_to_idx c =
  match ConstrHashtbl.find_opt (!constr_shareM) c with
  | None ->
     let v = fresh_constridx () in
     ConstrHashtbl.add (!constr_shareM) c v;
     v
  | Some v -> v
*)

(* --------------------------------------- *)
(* Tactic state sharing *)

(*
(* Shadowed identifiers in the tactic state *)
let tacst_ctx_shadowM = ref Names.Id.Map.empty
let clear_tacst_ctx_shadowM () = tacst_ctx_shadowM := Names.Id.Map.empty


(* Contexts in the tactic state *)
let tacst_ctxM = ref Names.Id.Map.empty
let clear_tacst_ctxM () = tacst_ctxM := Names.Id.Map.empty
let dump_shared_tacst_ctx_typM () =
  Names.Id.Map.iter (fun k (ty, _, _) -> print_string (Printf.sprintf "%s: %d\n" (Names.Id.to_string k) (share_constr ty))) !tacst_ctxM
let dump_pretty_tacst_ctx_typM () =
  Names.Id.Map.iter (fun k (_, pp_ty, _) -> print_string (Printf.sprintf "%s: %s\n" (Names.Id.to_string k) pp_ty)) !tacst_ctxM
let dump_shared_tacst_ctx_bodyM () =
  Names.Id.Map.iter (fun k (_, _, body) ->
    match body with
    | None -> ()
    | Some (body, _) -> print_string (Printf.sprintf "%s: %d\n" (Names.Id.to_string k) (share_constr body))) !tacst_ctxM
let dump_pretty_tacst_ctx_bodyM () =
  Names.Id.Map.iter (fun k (_, _, body) -> 
    match body with
    | None -> ()
    | Some (_, pp_body) -> print_string (Printf.sprintf "%s: %s\n" (Names.Id.to_string k) pp_body)) !tacst_ctxM


(* Goals in the tactic state *)
let tacst_goalM = ref IntMap.empty
let clear_tacst_goalM () = tacst_goalM := IntMap.empty
let add_goal cid env sigma concl =
  tacst_goalM := IntMap.add cid (pp2str (pr_goal_concl_style_env env sigma concl)) !tacst_goalM
(* NOTE(deh): No print because it's in shareM *)
let dump_pretty_tacst_goalM () = 
  IntMap.iter (fun k v -> print_string (Printf.sprintf "%d: %s\n" k v)) !tacst_goalM
*)

(* --------------------------------------- *)
(* Update context mappings in a tactic-state *)

(*
let gs_ctxid = GenSym.init ()
let fresh_ctxid () = GenSym.fresh gs_ctxid

(* Note(deh): 
 * Take care of shadowing when the same local identifier (in a different proof branch)
 * have different types.
 * 
 * tacst_ctx_idM: id -> [id]       (map identifiers to list of shadowed identifiers)
 * tacst_ctxM: id -> (typ, body)   (map identifier to type and/or body)
 *)

(* Take care of shadowing list *)
let add_ctx_id id id' =
  if Names.Id.Map.mem id !tacst_ctx_shadowM
  then (let ids = Names.Id.Map.find id !tacst_ctx_shadowM in
        tacst_ctx_shadowM := Names.Id.Map.add id (id' :: ids) !tacst_ctx_shadowM)
  else tacst_ctx_shadowM := Names.Id.Map.add id [id'] !tacst_ctx_shadowM

(* Get the list of shadowed variables *)
let find_ctx_id_shadowing id =
  if Names.Id.Map.mem id !tacst_ctx_shadowM
  then id :: Names.Id.Map.find id !tacst_ctx_shadowM
  else [id]

let add_ctx (typ, pr_typ, body) id =
  if Names.Id.Map.mem id !tacst_ctxM
  then
    let ids = find_ctx_id_shadowing id in
    let f id =
      match (Names.Id.Map.find id !tacst_ctxM, body) with
      | ((typ', _, Some (body', _)), Some (body, _)) ->
          Term.eq_constr typ typ' && Term.eq_constr body body'
      | ((typ', _, None), None) -> Term.eq_constr typ typ'
      | _ -> false
    in
    match List.find_opt f ids with
    | None ->
        let ctxid = fresh_ctxid() in
        let id' = Names.Id.of_string (Printf.sprintf "%s~%d" (Names.Id.to_string id) ctxid) in
        add_ctx_id id id';
        tacst_ctxM := Names.Id.Map.add id' (typ, pr_typ, body) !tacst_ctxM;
        id'
    | Some id' -> id'
  else (tacst_ctxM := Names.Id.Map.add id (typ, pr_typ, body) !tacst_ctxM; id)

let update_var_list_decl env sigma (l, c, typ) =
  let pbody = match c with
    | None -> None
    | Some c ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        Some (c, pp2str pb)
  in
  List.map (add_ctx (typ, pp2str (pr_ltype_env env sigma typ), pbody)) l

let update_rel_decl env sigma decl =
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
  (id, add_ctx (typ, pp2str (pr_ltype_env env sigma typ), body) id)

let update_context env sigma =
  let named_ids =
    Context.NamedList.fold
      (fun decl ids -> let ids' = update_var_list_decl env sigma decl in ids' @ ids)
      (Termops.compact_named_context (Environ.named_context env)) ~init:[]
  in
  let rel_ids = 
    Environ.fold_rel_context
      (fun env decl ids -> let (id, _) = update_rel_decl env sigma decl in id::ids)
      env ~init:[]
  in named_ids @ rel_ids
*)
