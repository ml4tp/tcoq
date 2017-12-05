open Names
open Term
open Pp
open Printer
open Vernacexpr

(* [Note] 
 *
 * Contains functionality for ML4TP. Prints out the tactic state of a Coq proof.
 * We output a "shared" representation of a Coq tactic state.
 *   1. Low-level format of expressions uses sharing
 *   2. Low-level format of tactic states just outputs identifiers and goal index
 *)


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

let rec show_ls f sep ls =
  String.concat sep (List.map f ls)

let rec show_arr f sep arr =
  let arr' = Array.map f arr in
  String.concat sep (Array.to_list arr')

let show_name name =
  match name with
  | Anonymous -> "$A"
  | Name id -> Names.Id.to_string id

let show_evar ev =
  Evar.repr ev


(* Other *)

let replace input output =
  Str.global_replace (Str.regexp_string input) output

let pp2str pp =
  replace "\n" " " (string_of_ppcmds (h 0 pp))



(* ************************************************************************** *)
(* Create shared Coq expressions *)


(* --------------------------------------- *)
(* Expression-level sharing *)

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
let constr_shareM = ref (ConstrHashtbl.create 100)
let clear_constr_shareM () = ConstrHashtbl.reset !constr_shareM

(* Map an index to its low-level expression *)
module IntMap = Map.Make(struct type t = int let compare = compare end)
let tacst_low_constrM = ref (IntMap.empty)
let clear_tacst_low_constrM () = tacst_low_constrM := IntMap.empty
let dump_low_constrM () = 
  IntMap.iter (fun k v -> print_string (Printf.sprintf "%d: %s\n" k v)) !tacst_low_constrM


let constr_to_idx c =
  match ConstrHashtbl.find_opt (!constr_shareM) c with
  | None ->
     let v = fresh_constridx () in
     ConstrHashtbl.add (!constr_shareM) c v;
     v
  | Some v -> v

let with_constr_idx k v =
  tacst_low_constrM := IntMap.add k v !tacst_low_constrM;
  k

let rec share_constr c =
  let idx = constr_to_idx c in
  match kind_of_term c with
  | Rel i -> with_constr_idx idx (Printf.sprintf "R %d" i)
  | Var id -> with_constr_idx idx (Printf.sprintf "V %s" (string_of_id id))
  | Meta mv -> with_constr_idx idx (Printf.sprintf "M %d" mv)
  | Evar (exk, cs) -> 
      let idxs = (share_constrs cs) in
      with_constr_idx idx (Printf.sprintf "E %d [%s]" (show_evar exk) idxs)
  | Sort sort -> with_constr_idx idx (Printf.sprintf "S %s" (string_of_ppcmds (Univ.Universe.pr (Sorts.univ_of_sort sort))))
  | Cast (c, ck, t) ->
      let idx1 = share_constr c in
      let idx2 = share_constr t in
      with_constr_idx idx (Printf.sprintf "CA %d %s %d" idx1 (share_cast_kind ck) idx2)
  | Prod (name, t1, t2) ->
      let idx1 = share_constr t1 in
      let idx2 = share_constr t2 in
      with_constr_idx idx (Printf.sprintf "P %s %d %d" (show_name name) idx1 idx2)
  | Lambda (name, t, c) -> 
      let idx1 = (share_constr t) in
      let idx2 = (share_constr c) in 
      with_constr_idx idx (Printf.sprintf "L %s %d %d" (show_name name) idx1 idx2)
  | LetIn (name, c1, t, c2) ->
      let idx1 = (share_constr c1) in
      let idx2 = (share_constr t) in  
      let idx3 = (share_constr c2) in  
      with_constr_idx idx (Printf.sprintf "LI %s %d %d %d" (show_name name) idx1 idx2 idx3)
  | App (c, cs) -> 
      let idx1 = (share_constr c) in
      let idxs = (share_constrs cs) in
      with_constr_idx idx (Printf.sprintf "A %d [%s]" idx1 idxs)
  | Const (const, ui) -> 
      with_constr_idx idx (Printf.sprintf "C %s [%s]" (Names.Constant.to_string const) (share_universe_instance ui))
  | Ind (ind, ui) ->
      let (mutind, pos) = share_inductive ind in
      with_constr_idx idx (Printf.sprintf "I %s %d [%s]" mutind pos (share_universe_instance ui))
  | Construct ((ind, conid), ui) ->
      let (mutind, pos) = share_inductive ind in
      with_constr_idx idx (Printf.sprintf "CO %s %d %d [%s]" mutind pos conid (share_universe_instance ui))
  | Case (ci, c1, c2, cs) ->
      let idx1 = share_constr c1 in
      let idx2 = share_constr c2 in
      let idxs = share_constrs cs in
      with_constr_idx idx (Printf.sprintf "CS [%s] %d %d [%s]" (share_case_info ci) idx1 idx2 idxs)
  | Fix ((iarr, i), pc) ->
      let (ns, ts, cs) = share_prec_declaration pc in
      with_constr_idx idx (Printf.sprintf "F [%s] %d [%s] [%s] [%s]" (share_int_arr iarr) i ns ts cs)
  | CoFix (i, pc) -> 
      let (ns, ts, cs) = share_prec_declaration pc in
      with_constr_idx idx (Printf.sprintf "CF %d [%s] [%s] [%s]" i ns ts cs)
  | Proj (proj, c) -> 
      let idx1 = share_constr c in
      with_constr_idx idx (Printf.sprintf "PJ %s %d" (Names.Projection.to_string proj) idx1)
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


(* --------------------------------------- *)
(* Tactic state sharing *)

(* Types in the tactic state *)
let tacst_ctx_typM = ref Names.Id.Map.empty
let clear_tacst_ctx_typM () = tacst_ctx_typM := Names.Id.Map.empty
let dump_shared_tacst_ctx_typM () =
  Names.Id.Map.iter (fun k (v, _) -> print_string (Printf.sprintf "%s: %d\n" (Names.Id.to_string k) (share_constr v))) !tacst_ctx_typM
let dump_pretty_tacst_ctx_typM () =
  Names.Id.Map.iter (fun k (_, str) -> print_string (Printf.sprintf "%s: %s\n" (Names.Id.to_string k) str)) !tacst_ctx_typM


(* Expression bodies in the tactic state *)
let tacst_ctx_bodyM = ref Names.Id.Map.empty
let clear_tacst_ctx_bodyM () = tacst_ctx_bodyM := Names.Id.Map.empty
let dump_shared_tacst_ctx_bodyM () =
  Names.Id.Map.iter (fun k (v, _) -> print_string (Printf.sprintf "%s: %d\n" (Names.Id.to_string k) (share_constr v))) !tacst_ctx_bodyM
let dump_pretty_tacst_ctx_bodyM () =
  Names.Id.Map.iter (fun k (_, str) -> print_string (Printf.sprintf "%s: %s\n" (Names.Id.to_string k) str)) !tacst_ctx_bodyM


(* Goals in the tactic state *)
let tacst_goalM = ref IntMap.empty
let clear_tacst_goalM () = tacst_goalM := IntMap.empty
let add_goal cid env sigma concl =
  tacst_goalM := IntMap.add cid (pp2str (pr_goal_concl_style_env env sigma concl)) !tacst_goalM
(* NOTE(deh): No print because it's in shareM *)
let dump_pretty_tacst_goalM () = 
  IntMap.iter (fun k v -> print_string (Printf.sprintf "%d: %s\n" k v)) !tacst_goalM


(* --------------------------------------- *)
(* Update context mappings in a tactic-state *)

let add_body c id =
  match c with
  | None -> ()
  | Some c -> tacst_ctx_bodyM := Names.Id.Map.add id c !tacst_ctx_bodyM

let add_typ typ id =
  tacst_ctx_typM := Names.Id.Map.add id typ !tacst_ctx_typM

let update_var_list_decl env sigma (l, c, typ) =
  let pbody = match c with
    | None -> None
    | Some c ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        Some (c, pp2str pb)
  in
  List.iter (add_body pbody) l;
  List.iter (add_typ (typ, pp2str (pr_ltype_env env sigma typ))) l;
  l

let gs_anon = GenSym.init ()
let fresh_anon () = GenSym.fresh gs_anon

let update_rel_decl env sigma decl =
  let open Context.Rel.Declaration in
  let na = get_name decl in
  let typ = get_type decl in
  let id = 
    match na with
    | Anonymous -> 
        let x = fresh_anon () in
        Names.Id.of_string (Printf.sprintf "ANON%d" x)
    | Name id -> id
  in
  let _ = 
    match decl with
    | LocalAssum _ -> ()
    | LocalDef (_, c, _) ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        add_body (Some (c, pp2str pb)) id 
  in
  (id, add_typ (typ, pp2str (pr_ltype_env env sigma typ)) id)

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
  clear_tacst_ctx_typM ();
  clear_tacst_ctx_bodyM ();
  clear_constr_shareM ();
  clear_tacst_goalM ();
  clear_tacst_low_constrM ()

let finalize_proof () =
  print_string "Typs\n";
  dump_shared_tacst_ctx_typM ();
  print_string "Bods\n";
  dump_shared_tacst_ctx_bodyM ();
  print_string "Constrs\n";
  dump_low_constrM ();
  print_string "PrTyps\n";
  dump_pretty_tacst_ctx_typM ();
  print_string "PrBods\n";
  dump_pretty_tacst_ctx_bodyM ();
  print_string "PrGls\n";
  dump_pretty_tacst_goalM ()

let rec show_vernac_typ_exp vt ve =
  match vt with
  | VtStartProof (name, _, names) -> 
      initialize_proof ();
      print_string (Printf.sprintf "bg(pf) {!} %s {!} %s\n" name (show_ls Names.Id.to_string ", " names))
  | VtSideff _ -> ()
  | VtQed _ ->
      finalize_proof ();
      print_string ("en(pf)\n")
  | VtProofStep _ ->
    begin
      match ve with
      | VernacSubproof _ -> print_string "bg(spf)\n"
      | VernacEndSubproof -> print_string "en(spf)\n"
      | _ -> ()
    end
  | VtProofMode _ -> ()
  | VtQuery (_, _) -> ()
  | VtStm (_, _) -> ()
  | VtUnknown -> ()








(* Junk *)

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
