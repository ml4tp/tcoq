open Names
open Term
open Pp
open Printer


(* Kludge counters *)

let deh_counter = ref 0
let deh_counter2 = ref 0
let deh_counter3 = ref 0
let deh_counter4 = ref 0

let deh_counter_inc () =
  let old = !deh_counter in
  deh_counter := (!deh_counter) + 1;
  old
  
let deh_counter2_inc () =
  let old = !deh_counter2 in
  deh_counter2 := (!deh_counter2) + 1;
  old

let deh_counter3_inc () =
  let old = !deh_counter3 in
  deh_counter3 := (!deh_counter3) + 1;
  old

let deh_counter4_inc () =
  let old = !deh_counter4 in
  deh_counter4 := (!deh_counter4) + 1;
  old


(* Showing *)

let rec deh_show_ls f sep ls =
  String.concat sep (List.map f ls)

let rec deh_show_arr f sep arr =
  let arr' = Array.map f arr in
  String.concat sep (Array.to_list arr')

let deh_show_name name =
  match name with
  | Anonymous -> "$A"
  | Name id -> Names.Id.to_string id

let deh_show_evar ev =
  Evar.repr ev


(* Shared data-structure utility *)

module ConstrHash =
  struct
    type t = Term.constr
    let equal c1 c2 = Term.eq_constr c1 c2
    let hash c = Term.hash_constr c
  end
module ConstrHashtbl = Hashtbl.Make(ConstrHash)
module IntMap = Map.Make(struct type t = int let compare = compare end)

let deh_shareM = ref (ConstrHashtbl.create 100)
let deh_lowconstrM = ref (IntMap.empty)
let deh_clear_shareM () = ConstrHashtbl.reset !deh_shareM
let deh_clear_lowconstrM () = deh_lowconstrM := IntMap.empty

let lookup_shareM c =
  match ConstrHashtbl.find_opt (!deh_shareM) c with
  | None ->
     let v = deh_counter3_inc() in
     ConstrHashtbl.add (!deh_shareM) c v;
     v
  | Some v -> v

let add_constrM k v =
  deh_lowconstrM := IntMap.add k v !deh_lowconstrM;
  k


(* Show shared data-structure *)

let rec share_constr c =
  let idx = lookup_shareM c in
  match kind_of_term c with
  | Rel i -> add_constrM idx (Printf.sprintf "R %d" i)
  | Var id -> add_constrM idx (Printf.sprintf "V %s" (string_of_id id))
  | Meta mv -> add_constrM idx (Printf.sprintf "M %d" mv)
  | Evar (exk, cs) -> 
      let idxs = (share_constrs cs) in
      add_constrM idx (Printf.sprintf "E %d [%s]" (deh_show_evar exk) idxs)
  | Sort sort -> add_constrM idx (Printf.sprintf "S %s" (string_of_ppcmds (Univ.Universe.pr (Sorts.univ_of_sort sort))))
  | Cast (c, ck, t) ->
      let idx1 = share_constr c in
      let idx2 = share_constr t in
      add_constrM idx (Printf.sprintf "CA %d %s %d" idx1 (share_cast_kind ck) idx2)
  | Prod (name, t1, t2) ->
      let idx1 = share_constr t1 in
      let idx2 = share_constr t2 in
      add_constrM idx (Printf.sprintf "P %s %d %d" (deh_show_name name) idx1 idx2)
  | Lambda (name, t, c) -> 
      let idx1 = (share_constr t) in
      let idx2 = (share_constr c) in 
      add_constrM idx (Printf.sprintf "L %s %d %d" (deh_show_name name) idx1 idx2)
  | LetIn (name, c1, t, c2) ->
      let idx1 = (share_constr c1) in
      let idx2 = (share_constr t) in  
      let idx3 = (share_constr c2) in  
      add_constrM idx (Printf.sprintf "LI %s %d %d %d" (deh_show_name name) idx1 idx2 idx3)
  | App (c, cs) -> 
      let idx1 = (share_constr c) in
      let idxs = (share_constrs cs) in
      add_constrM idx (Printf.sprintf "A %d [%s]" idx1 idxs)
  | Const (const, ui) -> 
      add_constrM idx (Printf.sprintf "C %s [%s]" (Names.Constant.to_string const) (share_universe_instance ui))
  | Ind (ind, ui) ->
      let (s, i) = share_inductive ind in
      add_constrM idx (Printf.sprintf "I %s %d [%s]" s i (share_universe_instance ui))
  | Construct ((ind, j), ui) ->
      let (s, i) = share_inductive ind in
      add_constrM idx (Printf.sprintf "CO %s %d %d [%s]" s i j (share_universe_instance ui))
  | Case (ci, c1, c2, cs) ->
      let idx1 = share_constr c1 in
      let idx2 = share_constr c2 in
      let idxs = share_constrs cs in
      add_constrM idx (Printf.sprintf "CS [%s] %d %d [%s]" (share_case_info ci) idx1 idx2 idxs)
  | Fix ((iarr, i), pc) ->
      let (ns, ts, cs) = share_prec_declaration pc in
      add_constrM idx (Printf.sprintf "F [%s] %d [%s] [%s] [%s]" (share_int_arr iarr) i ns ts cs)
  | CoFix (i, pc) -> 
      let (ns, ts, cs) = share_prec_declaration pc in
      add_constrM idx (Printf.sprintf "CF %d [%s] [%s] [%s]" i ns ts cs)
  | Proj (proj, c) -> 
      let idx1 = share_constr c in
      add_constrM idx (Printf.sprintf "PJ %s %d" (Names.Projection.to_string proj) idx1)
and share_constrs cs =
  deh_show_arr (fun c -> string_of_int (share_constr c)) " " cs
and share_cast_kind ck =
  match ck with
  | VMcast -> "V"
  | NATIVEcast -> "N"
  | DEFAULTcast -> "D"
  | REVERTcast -> "R"
and share_universe_instance ui =
  deh_show_arr Univ.Level.to_string " " (Univ.Instance.to_array ui)
and share_inductive (mutind, i) =
  (Names.MutInd.to_string mutind, i)
and share_prec_declaration (names, types, constrs) =
  let names' = deh_show_arr deh_show_name " " names in
  let types' = share_constrs types in
  let constrs' = share_constrs constrs in
  (names', types', constrs')
and share_int_arr iarr =
  deh_show_arr string_of_int " " iarr
and share_case_info ci =
  let (mutind, i) = share_inductive ci.ci_ind in
  Printf.sprintf "%s %d %d %s %s" mutind i (ci.ci_npar) (share_int_arr ci.ci_cstr_ndecls) (share_int_arr ci.ci_cstr_nargs)


(* Showing type and expression contexts *)

let deh_typM = ref Names.Id.Map.empty
let deh_constrM = ref Names.Id.Map.empty
let deh_goalM = ref IntMap.empty
let deh_clear_typM () = deh_typM := Names.Id.Map.empty
let deh_clear_constrM () = deh_constrM := Names.Id.Map.empty
let deh_clear_goalM () = deh_goalM := IntMap.empty

let replace input output =
  Str.global_replace (Str.regexp_string input) output

let deh_pp2str pp =
  replace "\n" " " (string_of_ppcmds (h 0 pp))

let deh_add_body c id =
  match c with
  | None -> ()
  | Some c -> deh_constrM := Names.Id.Map.add id c !deh_constrM

let deh_add_typ typ id =
  deh_typM := Names.Id.Map.add id typ !deh_typM

let deh_update_var_list_decl env sigma (l, c, typ) =
  let pbody = match c with
    | None -> None
    | Some c ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        Some (c, deh_pp2str pb)
  in
  List.iter (deh_add_body pbody) l;
  List.iter (deh_add_typ (typ, deh_pp2str (pr_ltype_env env sigma typ))) l;
  l

let deh_update_rel_decl env sigma decl =
  let open Context.Rel.Declaration in
  let na = get_name decl in
  let typ = get_type decl in
  let id = 
    match na with
    | Anonymous -> 
        let x = deh_counter4_inc() in
        Names.Id.of_string (Printf.sprintf "ANON%d" x)
    | Name id -> id
  in
  let _ = 
    match decl with
    | LocalAssum _ -> ()
    | LocalDef (_, c, _) ->
        let pb = pr_lconstr_env env sigma c in
        let pb = if isCast c then surround pb else pb in
        deh_add_body (Some (c, deh_pp2str pb)) id 
  in
  (id, deh_add_typ (typ, deh_pp2str (pr_ltype_env env sigma typ)) id)

let deh_update_context env sigma =
  let named_ids =
    Context.NamedList.fold
      (fun decl ids -> let ids' = deh_update_var_list_decl env sigma decl in ids' @ ids)
      (Termops.compact_named_context (Environ.named_context env)) ~init:[]
  in
  let rel_ids = 
    Environ.fold_rel_context
      (fun env decl ids -> let (id, _) = deh_update_rel_decl env sigma decl in id::ids)
      env ~init:[]
  in named_ids @ rel_ids

let deh_add_goal cid env sigma concl =
  deh_goalM := IntMap.add cid (deh_pp2str (pr_goal_concl_style_env env sigma concl)) !deh_goalM


(* Printing contexts *)

let deh_print_typM () =
  Names.Id.Map.iter (fun k (v, _) -> print_string (Printf.sprintf "%s: %d\n" (Names.Id.to_string k) (share_constr v))) !deh_typM

let deh_print_constrM () =
  Names.Id.Map.iter (fun k (v, _) -> print_string (Printf.sprintf "%s: %d\n" (Names.Id.to_string k) (share_constr v))) !deh_constrM

let deh_print_lowconstrM () = 
  IntMap.iter (fun k v -> print_string (Printf.sprintf "%d: %s\n" k v)) !deh_lowconstrM

let deh_pr_typM () =
  Names.Id.Map.iter (fun k (_, str) -> print_string (Printf.sprintf "%s: %s\n" (Names.Id.to_string k) str)) !deh_typM

let deh_pr_constrM () =
  Names.Id.Map.iter (fun k (_, str) -> print_string (Printf.sprintf "%s: %s\n" (Names.Id.to_string k) str)) !deh_constrM

let deh_pr_goalM () = 
  IntMap.iter (fun k v -> print_string (Printf.sprintf "%d: %s\n" k v)) !deh_goalM






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


(*
let rec deh_show_ls sep show_fn ls =
  match ls with
  | [] -> ""
  | hd::[] -> show_fn hd
  | hd::tl -> Printf.sprintf "%s%s%s" (show_fn hd) sep (deh_show_ls sep show_fn tl)
*)

(*
let deh_show_var_decl_skel f env sigma (id, c, typ) =
  let pbody =
    match c with
    | None ->  ""
    | Some c -> " := " ^ deh_show_constr c
  in
  let pt = deh_show_constr typ in
  Printf.sprintf "%s%s : %s" (f id) pbody pt
*)

(*
let deh_show_var_decl f env sigma d =
  deh_show_var_decl_skel f env sigma (Context.Named.Declaration.to_tuple d)
*)

(*
let deh_show_var_list_decl env sigma (l, c, typ) =
  deh_show_var_decl_skel (fun ids -> deh_show_ls Names.Id.to_string ", " ids) env sigma (l,c,typ) 
*)

(*
let deh_show_rel_decl env sigma decl =
  let open Context.Rel.Declaration in
  let na = get_name decl in
  let typ = get_type decl in
  let pbody = match decl with
    | LocalAssum _ -> ""
    | LocalDef (_,c,_) -> " := " ^ deh_show_constr c
  in
  let ptyp = deh_show_constr typ in
  match na with
  | Anonymous -> 
      Printf.sprintf "<> %s : %s" pbody ptyp
  | Name id -> 
      Printf.sprintf "%s %s : %s" (Names.Id.to_string id) pbody ptyp
*)

(*
let deh_show_context env sigma =
  let sign_env =
    Context.NamedList.fold
      (fun d pps ->
         let pidt =  deh_show_var_list_decl env sigma d in
         (pps ^ "\n" ^ pidt))
      (Termops.compact_named_context (Environ.named_context env)) ~init:("")
  in
  let db_env =
    Environ.fold_rel_context
      (fun env d pps ->
         let pnat = deh_show_rel_decl env sigma d in (pps ^ "\n" ^ pnat))
      env ~init:("")
  in
  (sign_env ^ db_env)
*)


(*
let rec deh_show_constr c =
  match kind_of_term c with
  | Rel i -> Printf.sprintf "R(%d)" i
  | Var id -> Printf.sprintf "V(%s)" (string_of_id id)
  | Meta mv -> Printf.sprintf "M(%d)" mv
  | Evar (exk, cs) -> Printf.sprintf "E(%d, (%s))" (deh_show_evar exk) (deh_show_arr deh_show_constr ", " cs)
  | Sort sort -> Printf.sprintf "S(%s)" (string_of_ppcmds (Univ.Universe.pr (Sorts.univ_of_sort sort)))
  | Cast (c, ck, t) -> Printf.sprintf "CA(%s, %s, %s)" (deh_show_constr c) (deh_show_cast_kind ck) (deh_show_constr t)
  | Prod (name, t1, t2) -> Printf.sprintf "P(%s, %s, %s)" (deh_show_name name) (deh_show_constr t1) (deh_show_constr t2)
  | Lambda (name, t, c) -> Printf.sprintf "L(%s, %s, %s)" (deh_show_name name) (deh_show_constr t) (deh_show_constr c)
  | LetIn (name, c1, t, c2) -> Printf.sprintf "LI(%s, %s, %s, %s)" (deh_show_name name) (deh_show_constr c1) (deh_show_constr t) (deh_show_constr c2)
  | App (c, cs) -> Printf.sprintf "A(%s, (%s))" (deh_show_constr c) (deh_show_arr deh_show_constr ", " cs)
  | Const (const, ui) -> Printf.sprintf "C(%s, (%s))" (Names.Constant.to_string const) (deh_show_universe_instance ui)
  | Ind (ind, ui) -> Printf.sprintf "I(%s, (%s))" (deh_show_inductive ind) (deh_show_universe_instance ui)
  | Construct ((ind, j), ui) -> Printf.sprintf "CO((%s, %d), (%s))" (deh_show_inductive ind) j (deh_show_universe_instance ui)
  | Case (ci, c1, c2, cs) -> Printf.sprintf "CS(%s, %s, %s, %s)" (deh_show_case_info ci) (deh_show_constr c1) (deh_show_constr c2) (deh_show_arr deh_show_constr ", " cs)
  | Fix ((iarr, i), pc) -> Printf.sprintf "F((%s, %d), %s)" (deh_show_int_arr iarr) i (deh_show_prec_declaration pc)
  | CoFix (i, pc) -> Printf.sprintf "CF(%d, %s)" i (deh_show_prec_declaration pc)
  | Proj (proj, c) -> Printf.sprintf "PJ(%s, %s)" (Names.Projection.to_string proj) (deh_show_constr c)
and deh_show_cast_kind ck =
  match ck with
  | VMcast -> "V"
  | NATIVEcast -> "N"
  | DEFAULTcast -> "D"
  | REVERTcast -> "R"
and deh_show_universe_instance ui =
  deh_show_arr Univ.Level.to_string ", " (Univ.Instance.to_array ui)
and deh_show_prec_declaration (names, types, constrs) =
  let names' = deh_show_arr deh_show_name ", " names in
  let types' = deh_show_arr deh_show_constr ", " types in
  let constrs' = deh_show_arr deh_show_constr ", " constrs in
  Printf.sprintf "((%s), (%s), (%s))" names' types' constrs'
and deh_show_inductive (mutind, i) =
  Printf.sprintf "(%s, %d)" (Names.MutInd.to_string mutind) i
and deh_show_int_arr iarr =
  deh_show_arr string_of_int ", " iarr
and deh_show_case_info ci =
  Printf.sprintf "(%s, %d, %s, %s)" (deh_show_inductive ci.ci_ind) (ci.ci_npar) (deh_show_int_arr ci.ci_cstr_ndecls) (deh_show_int_arr ci.ci_cstr_nargs)
*)
