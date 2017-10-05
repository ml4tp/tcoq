(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Author: Jean-Christophe Filliâtre as part of the rebuilding of Coq
   around a purely functional abstract type-checker, Aug 1999 *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Flag for predicativity of Set by Hugo Herbelin in Oct 2003 *)
(* Support for virtual machine by Benjamin Grégoire in Oct 2004 *)
(* Support for retroknowledge by Arnaud Spiwack in May 2007 *)
(* Support for assumption dependencies by Arnaud Spiwack in May 2007 *)

(* Miscellaneous maintenance by Bruno Barras, Hugo Herbelin, Jean-Marc
   Notin, Matthieu Sozeau *)

(* This file defines the type of environments on which the
   type-checker works, together with simple related functions *)

open CErrors
open Util
open Names
open Term
open Vars
open Declarations
open Pre_env
open Context.Rel.Declaration

(* The type of environments. *)

type named_context_val = Pre_env.named_context_val

type env = Pre_env.env


let rec deh_print_tab tab str =
  if tab <= 0 
  then print_string str 
  else (print_string " "; deh_print_tab (tab - 1) str)

let dan_print_option print opt =
  match opt with
  | None -> print_string "None"
  | Some x -> 
      print_string "Some(" ;
      print x ;
      print_string ")"

let dan_print_pair print_l print_r (l, r) =
  print_string "(" ;
  print_l l ;
  print_string ", " ;
  print_r r ;
  print_string ")"

let rec deh_print_ls sep print_fn ls =
    match ls with
    | [] -> ()
    | hd::[] -> print_fn hd
    | hd::tl -> print_fn hd; print_string sep; deh_print_ls sep print_fn tl

let deh_show_name name =
  match name with
  | Name.Anonymous -> "Anon"
  | Name.Name id -> Id.to_string id

let deh_show_evar ev =
  string_of_int (Evar.repr ev)

let deh_print_array sep print arr =
  let last_idx = Array.length arr - 1 in
  Array.iteri (fun i x -> print x; if i < last_idx then print_string sep else ()) arr

(*
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of sorts
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant puniverses
  | Ind       of inductive puniverses
  | Construct of constructor puniverses
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of projection * 'constr
*)
let rec dan_print_constr constr = 
  match Constr.kind constr with
  | Constr.Rel i ->  
      print_string "Rel(";
      print_string (string_of_int i);
      print_string ")"
  | Constr.Var id -> 
      print_string "Var(";
      print_string (Id.to_string id);
      print_string ")"
  | Evar pex -> 
      print_string "Evar(";
      deh_print_pexistential pex;
      print_string ")"
  | Sort sorts -> 
      print_string "Sort(";
      print_string "TODO(sorts)";
      print_string ")"
  | Cast (constr, ck, ty) -> 
      print_string "Cast(";
      dan_print_constr constr;
      print_string ", ";
      print_string "TODO(cast_kind)";
      print_string ", ";
      dan_print_constr ty;
      print_string ")"
  | Prod (name, ty1, ty2) -> 
      print_string "Prod(";
      print_string (deh_show_name name);
      print_string ", ";
      dan_print_constr ty1; 
      print_string ", ";
      dan_print_constr ty2; 
      print_string ")"
  | Lambda (name, ty, constr') -> 
      print_string "Lambda(";
      print_string (deh_show_name name); 
      print_string ", ";
      dan_print_constr ty; 
      print_string ", ";
      dan_print_constr constr';
      print_string ")"
  | LetIn (name, constr1, ty, constr2) -> 
      print_string "LetIn(";
      dan_print_constr constr1;
      print_string ", ";
      dan_print_constr ty;
      print_string ", ";
      dan_print_constr constr2;
      print_string ")"
  | App (constr', constrs) -> 
      print_string "App(";
      dan_print_constr constr'; 
      print_string ", ";
      deh_print_array ", " dan_print_constr constrs;
      print_string ")"
  | Const consts -> 
      print_string "Const(";
      deh_print_puniverses (fun x -> print_string (Names.string_of_con x)) consts;
      print_string ")"
  | Ind ind -> 
      print_string "Ind(";
      deh_print_inductive ind;
      print_string ")"
  | Construct ctor -> 
      print_string "Construct";
      deh_print_construct ctor;
      print_string ")"
  | Case (_, constr1, constr2, constrs) -> 
      print_string "Case(";
      print_string "TODO(case_info)";
      print_string ", ";
      dan_print_constr constr1;
      print_string ", ";
      dan_print_constr constr2;
      print_string ", ";
      deh_print_array ", " dan_print_constr constrs;
      print_string ")"
  | Fix ((is, i), (names, tys, constrs)) -> 
      print_string "Fix(";
      deh_print_array ", " (fun x -> print_string (deh_show_name x)) names;
      print_string ", ";
      deh_print_array ", " dan_print_constr tys;
      print_string ", ";
      deh_print_array ", " dan_print_constr constrs;
      print_string ")"
  | CoFix (i, (names, tys, constrs)) -> 
      print_string "CoFix(";
      deh_print_array ", " (fun x -> print_string (deh_show_name x)) names;
      print_string ", ";
      deh_print_array ", " dan_print_constr tys;
      print_string ", ";
      deh_print_array ", " dan_print_constr constrs;
      print_string ")"
  | Proj (prj, constr) -> 
      print_string "Proj(";
      print_string "TODO(projection)";
      print_string ", ";
      dan_print_constr constr;
      print_string ")"
and deh_print_pexistential (eky, constrs) =
  (* type 'constr pexistential = existential_key * 'constr array *)
  print_string (deh_show_evar eky);
  print_string ", ";
  deh_print_array ", " dan_print_constr constrs
and deh_print_puniverses print (x, inst) =
  print x;
  print_string ", ";
  deh_print_array ", " (fun x -> print_string (Univ.Level.to_string x)) (Univ.Instance.to_array inst)
and deh_print_inductive ((mi, i), inst) =
  print_string (Names.MutInd.to_string mi);
  print_string ", ";
  print_string (string_of_int i) ;
  print_string ", ";
  deh_print_array ", " (fun x -> print_string (Univ.Level.to_string x)) (Univ.Instance.to_array inst)
and deh_print_construct (((mi, i1), i2), inst) =
  print_string (Names.MutInd.to_string mi);
  print_string ", ";
  print_string (string_of_int i1);
  print_string ", ";
  print_string (string_of_int i2);
  print_string ", ";
  deh_print_array ", " (fun x -> print_string (Univ.Level.to_string x)) (Univ.Instance.to_array inst)


let dan_print_substituted print sub =
  (* print sub.subst_value ; *)
  print_string "TODO(substituted)"

let dan_print_constr_substituted cs =
  dan_print_constr (Mod_subst.force_constr cs)
  (* dan_print_substituted Print.print_pure_constr cs *)


let dan_print_lazy_constr lc =
  print_string "TODO(lazy_constr)"
  (*
  match lc with
  | Indirect (subs, dp, i) ->
      print_string "Indirect(" ;
      dan_print_ls dan_print_substitution ", " subs ;
      print_string ", " ;
      dan_print_dir_path dp ; 
      print_string ", " ;
      print_int i ;
      print_string ")"
    *)

let dan_print_constant_def cd =
  match cd with
  | Undef i -> 
      print_string "Undef(" ;
      (* dan_print_inline i ; *)
      print_string ")"
  | Def cs -> 
      print_string "Def(" ;
      dan_print_constr_substituted cs ;
      print_string ")"
  | OpaqueDef lc -> 
      print_string "OpaqueDef(" ;
      dan_print_lazy_constr lc ;
      print_string ")"

let dan_print_universe_context uc = 
    print_string "TODO(universe_context)"

(*
let dan_print_constant_universes cu =
  match cu with
  | Cic.Monomorphic_const uc -> print_string "Monomorphic_const(TODO)"
  | Cic.Polymorphic_const auc -> print_string "Polymorphic_const(TODO)"
*)

let dan_print_projection_body pb =
  print_string "{ " ;
  print_string "proj_ind: " ;
  print_string ", proj_npars: " ;
  print_int pb.proj_npars ;
  print_string ", proj_arg: " ;
  print_int pb.proj_arg ;
  print_string ", proj_type: " ;
  dan_print_constr pb.proj_type ;
  print_string ", proj_eta: " ;
  dan_print_pair dan_print_constr dan_print_constr pb.proj_eta ;
  print_string ", proj_body: " ;
  dan_print_constr pb.proj_body ;
  print_string " }"

let dan_print_typing_flags tf =
  print_string "{ " ;
  print_string "check_guarded: " ;
  print_string (string_of_bool tf.check_guarded) ;
  print_string ", check_universe: " ;
  print_string (string_of_bool tf.check_universes) ;
  print_string " }"

(*
  type constant_body = {
    const_hyps : Context.section_context; (** New: younger hyp at top *)
    const_body : constant_def;
    const_type : constant_type;
    const_body_code : Cemitcodes.to_patch_substituted option;
    const_polymorphic : bool; (** Is it polymorphic or not *)
    const_universes : constant_universes;
    const_proj : projection_body option;
    const_inline_code : bool;
    const_typing_flags : typing_flags; (** The typing options which
                                           were used for
                                           type-checking. *)
}
*)
let dan_print_constant_body cb =
  (* print_string "{ " ; *)
  (* print_string "const_body: " ; *)
  dan_print_constant_def cb.const_body
  (* print_string ",\nconst_type: " ; *)
  (* dan_print_constr cb.Cconst_type ; *)
  (* print_string ",\nconst_body_code: UNUSED" ; *)
  (* print_string ",\nconst_universes: TODO" ; *)
  (* dan_print_constant_universes cb.const_universes ; *)
  (* print_string ",\nconst_proj: " ; *)
  (* dan_print_option dan_print_projection_body cb.const_proj ; *)
  (* print_string ",\nconst_inline_code: " ; *)
  (* print_string (string_of_bool cb.const_inline_code) ; *)
  (* print_string ",\nconst_typing_flags: " ; *)
  (* dan_print_typing_flags cb.const_typing_flags ; *)
  (* print_string " }" *)

let deh_print_constant_body cb =
  dan_print_constant_body cb

let deh_print_constant_key (cb, (li, key)) =
  deh_print_constant_body cb

(*
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}
*)
let deh_print_globals tab globs =
  deh_print_tab tab "globals = {\n";
  let tab = tab + 2 in
  deh_print_tab tab "env_constants:";
  (* kernel/names.ml:module Cmap_env = HMap.Make(Constant.UserOrd) *)
  Cmap_env.iter (fun k v -> deh_print_constant_key v) (globs.env_constants);
  (* deh_print_tab tab globs.env_constants; *)
  deh_print_tab tab "env_inductives: TODO";
  deh_print_tab tab "env_modules: TODO";
  deh_print_tab tab "env_modtypes: TODO";
  deh_print_tab (tab - 2) "}\n"

let deh_print_name_id id =
  print_string (Names.Id.to_string id)

let deh_print_declaration decl =
  match decl with
  | Context.Named.Declaration.LocalAssum (id, constr) ->
      print_string "LocalAssum(";
      deh_print_name_id id;
      print_string ", ";
      dan_print_constr constr;
      print_string ")"
  | Context.Named.Declaration.LocalDef (id, constr1, constr2) ->
      print_string "LocalDef(";
      deh_print_name_id id;
      print_string ", ";
      dan_print_constr constr1;
      print_string ", ";
      dan_print_constr constr2;
      print_string ")"

let deh_print_id_decl_fval (id, decl, fval) =
  print_string "(";
  deh_print_name_id id;
  print_string ",";
  deh_print_declaration decl;
  print_string ",";
  print_string "TODO(deh: fval)";
  print_string ")"

let deh_print_env_named_context tab named_context =
  (* Context.Named.t *)
  deh_print_tab tab "env_named_ctx: ";
  let env_named_ctx = named_context.env_named_ctx in
  Context.Named.iter (fun x -> dan_print_constr x) env_named_ctx;
  print_string ";\n";
  (* Context.Named.Declaration.t * lazy_val) Id.Map.t; *) 
  deh_print_tab tab "env_named_map: ";
  let env_named_map = named_context.env_named_map in
  let env_named_map_dom = Names.Id.Set.elements (Id.Map.domain env_named_map) in
  let f = (fun id -> let (decl, lval) = Id.Map.get id env_named_map in
                     (id, decl, force_lazy_val lval)) in
  let ids_decls_fvals = List.map f env_named_map_dom in
  deh_print_ls ", " deh_print_id_decl_fval ids_decls_fvals;
  print_string ";\n"

(* 
  env_globals       : globals;
  env_named_context : named_context_val;
  env_rel_context   : Context.Rel.t;
  env_rel_val       : lazy_val list;
  env_nb_rel        : int;
  env_stratification : stratification;
  env_typing_flags  : typing_flags;
  env_conv_oracle   : Conv_oracle.oracle;
  retroknowledge : Retroknowledge.retroknowledge;
  indirect_pterms : Opaqueproof.opaquetab;
*)
let deh_print_env tab env =
  deh_print_tab tab "env = {\n" ;
  let tab = tab + 2 in
  (* deh_print_tab tab "env_globals:"; *)
  (* deh_print_globals tab env.env_globals; *)
  deh_print_env_named_context tab env.env_named_context;
  deh_print_tab tab "env_rel_context: ";
  Context.Rel.iter (fun x -> print_string "hi") (env.env_rel_context);
  (* print_string (Pp.string_of_ppcmds (Printer.pr_context_unlimited env Evd.empty)); *)
  (* deh_print_tab tab "\nenv_rel_val: TODO"; *)
  (* deh_print_tab tab ("\nenv_nb_rel: " ^ string_of_int env.env_nb_rel); *)
  (* deh_print_tab tab "\nenv_stratification: TODO"; *)
  (* deh_print_tab tab "\nenv_typing_flags: TODO"; *)
  (* deh_print_tab tab "\nenv_conv_oracle: TODO"; *)
  (* deh_print_tab tab "\nretroknowledge: TODO"; *)
  (* deh_print_tab tab "\nindirect_pterms: TODO" *)
  deh_print_tab (tab - 2) "}\n"

let pre_env env = env
let env_of_pre_env env = env
let oracle env = env.env_conv_oracle
let set_oracle env o = { env with env_conv_oracle = o }

let empty_named_context_val = empty_named_context_val

let empty_env = empty_env

let engagement env = env.env_stratification.env_engagement
let typing_flags env = env.env_typing_flags

let is_impredicative_set env = 
  match engagement env with
  | ImpredicativeSet -> true
  | _ -> false

let type_in_type env = not (typing_flags env).check_universes
let deactivated_guard env = not (typing_flags env).check_guarded

let universes env = env.env_stratification.env_universes
let named_context env = env.env_named_context.env_named_ctx
let named_context_val env = env.env_named_context
let rel_context env = env.env_rel_context
let opaque_tables env = env.indirect_pterms
let set_opaque_tables env indirect_pterms = { env with indirect_pterms }

let empty_context env =
  match env.env_rel_context, env.env_named_context.env_named_ctx with
  | [], [] -> true
  | _ -> false

(* Rel context *)
let lookup_rel n env =
  Context.Rel.lookup n env.env_rel_context

let evaluable_rel n env =
  is_local_def (lookup_rel n env)

let nb_rel env = env.env_nb_rel

let push_rel = push_rel

let push_rel_context ctxt x = Context.Rel.fold_outside push_rel ctxt ~init:x

let push_rec_types (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

let fold_rel_context f env ~init =
  let rec fold_right env =
    match env.env_rel_context with
    | [] -> init
    | rd::rc ->
	let env =
	  { env with
	    env_rel_context = rc;
	    env_rel_val = List.tl env.env_rel_val;
	    env_nb_rel = env.env_nb_rel - 1 } in
	f env rd (fold_right env)
  in fold_right env

(* Named context *)

let named_context_of_val c = c.env_named_ctx

(* [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t *)
let map_named_val = map_named_val

let empty_named_context = Context.Named.empty

let push_named = push_named
let push_named_context = List.fold_right push_named
let push_named_context_val = push_named_context_val

let val_of_named_context ctxt =
  List.fold_right push_named_context_val ctxt empty_named_context_val


let lookup_named = lookup_named
let lookup_named_val id ctxt = fst (Id.Map.find id ctxt.env_named_map)

let eq_named_context_val c1 c2 =
   c1 == c2 || Context.Named.equal (named_context_of_val c1) (named_context_of_val c2)

(* A local const is evaluable if it is defined  *)

open Context.Named.Declaration

let named_type id env =
  get_type (lookup_named id env)

let named_body id env =
  get_value (lookup_named id env)

let evaluable_named id env =
  match named_body id env with
  | Some _      -> true
  | _          -> false

let reset_with_named_context ctxt env =
  { env with
    env_named_context = ctxt;
    env_rel_context = Context.Rel.empty;
    env_rel_val = [];
    env_nb_rel = 0 }

let reset_context = reset_with_named_context empty_named_context_val

let pop_rel_context n env =
  let ctxt = env.env_rel_context in
  { env with
    env_rel_context = List.skipn n ctxt;
    env_nb_rel = env.env_nb_rel - n }

let fold_named_context f env ~init =
  let rec fold_right env =
    match match_named_context_val env.env_named_context with
    | None -> init
    | Some (d, v, rem) ->
	let env =
	  reset_with_named_context rem env in
	f env d (fold_right env)
  in fold_right env

let fold_named_context_reverse f ~init env =
  Context.Named.fold_inside f ~init:init (named_context env)


(* Universe constraints *)

let map_universes f env =
  let s = env.env_stratification in
    { env with env_stratification =
	 { s with env_universes = f s.env_universes } }
				     
let add_constraints c env =
  if Univ.Constraint.is_empty c then env
  else map_universes (UGraph.merge_constraints c) env

let check_constraints c env =
  UGraph.check_constraints c env.env_stratification.env_universes

let push_constraints_to_env (_,univs) env =
  add_constraints univs env

let add_universes strict ctx g =
  let g = Array.fold_left
	    (* Be lenient, module typing reintroduces universes and constraints due to includes *)
	    (fun g v -> try UGraph.add_universe v strict g with UGraph.AlreadyDeclared -> g)
	    g (Univ.Instance.to_array (Univ.UContext.instance ctx))
  in
    UGraph.merge_constraints (Univ.UContext.constraints ctx) g
			   
let push_context ?(strict=false) ctx env =
  map_universes (add_universes strict ctx) env

let add_universes_set strict ctx g =
  let g = Univ.LSet.fold
	    (fun v g -> try UGraph.add_universe v strict g with UGraph.AlreadyDeclared -> g)
	    (Univ.ContextSet.levels ctx) g
  in UGraph.merge_constraints (Univ.ContextSet.constraints ctx) g

let push_context_set ?(strict=false) ctx env =
  map_universes (add_universes_set strict ctx) env

let set_engagement c env = (* Unsafe *)
  { env with env_stratification =
    { env.env_stratification with env_engagement = c } }

let set_typing_flags c env = (* Unsafe *)
  { env with env_typing_flags = c }

(* Global constants *)

let lookup_constant = lookup_constant

let no_link_info = NotLinked

let add_constant_key kn cb linkinfo env =
  let new_constants =
    Cmap_env.add kn (cb,(ref linkinfo, ref None)) env.env_globals.env_constants in
  let new_globals =
    { env.env_globals with
	env_constants = new_constants } in
  { env with env_globals = new_globals }

let add_constant kn cb env =
  add_constant_key kn cb no_link_info env

let constraints_of cb u =
  let univs = cb.const_universes in
    Univ.subst_instance_constraints u (Univ.UContext.constraints univs)

let map_regular_arity f = function
  | RegularArity a as ar -> 
    let a' = f a in 
      if a' == a then ar else RegularArity a'
  | TemplateArity _ -> assert false

(* constant_type gives the type of a constant *)
let constant_type env (kn,u) =
  let cb = lookup_constant kn env in
    if cb.const_polymorphic then
      let csts = constraints_of cb u in
	(map_regular_arity (subst_instance_constr u) cb.const_type, csts)
    else cb.const_type, Univ.Constraint.empty

let constant_context env kn =
  let cb = lookup_constant kn env in
    if cb.const_polymorphic then cb.const_universes
    else Univ.UContext.empty

type const_evaluation_result = NoBody | Opaque | IsProj

exception NotEvaluableConst of const_evaluation_result

let constant_value env (kn,u) =
  let cb = lookup_constant kn env in
    if cb.const_proj = None then
      match cb.const_body with
      | Def l_body -> 
	if cb.const_polymorphic then
	  let csts = constraints_of cb u in
	    (subst_instance_constr u (Mod_subst.force_constr l_body), csts)
	else Mod_subst.force_constr l_body, Univ.Constraint.empty
      | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
      | Undef _ -> raise (NotEvaluableConst NoBody)
    else raise (NotEvaluableConst IsProj)

let constant_opt_value env cst =
  try Some (constant_value env cst)
  with NotEvaluableConst _ -> None

let constant_value_and_type env (kn, u) =
  let cb = lookup_constant kn env in
    if cb.const_polymorphic then
      let cst = constraints_of cb u in
      let b' = match cb.const_body with
	| Def l_body -> Some (subst_instance_constr u (Mod_subst.force_constr l_body))
	| OpaqueDef _ -> None
	| Undef _ -> None
      in
	b', map_regular_arity (subst_instance_constr u) cb.const_type, cst
    else 
      let b' = match cb.const_body with
	| Def l_body -> Some (Mod_subst.force_constr l_body)
	| OpaqueDef _ -> None
	| Undef _ -> None
      in b', cb.const_type, Univ.Constraint.empty

(* These functions should be called under the invariant that [env] 
   already contains the constraints corresponding to the constant 
   application. *)

(* constant_type gives the type of a constant *)
let constant_type_in env (kn,u) =
  let cb = lookup_constant kn env in
    if cb.const_polymorphic then
      map_regular_arity (subst_instance_constr u) cb.const_type
    else cb.const_type

let constant_value_in env (kn,u) =
  let cb = lookup_constant kn env in
  match cb.const_body with
    | Def l_body -> 
      let b = Mod_subst.force_constr l_body in
	subst_instance_constr u b
    | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
    | Undef _ -> raise (NotEvaluableConst NoBody)

let constant_opt_value_in env cst =
  try Some (constant_value_in env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant kn env =
  let cb = lookup_constant kn env in
    match cb.const_body with
    | Def _ -> true
    | OpaqueDef _ -> false
    | Undef _ -> false

let polymorphic_constant cst env =
  (lookup_constant cst env).const_polymorphic

let polymorphic_pconstant (cst,u) env =
  if Univ.Instance.is_empty u then false
  else polymorphic_constant cst env

let type_in_type_constant cst env =
  not (lookup_constant cst env).const_typing_flags.check_universes

let template_polymorphic_constant cst env =
  match (lookup_constant cst env).const_type with 
  | TemplateArity _ -> true
  | RegularArity _ -> false

let template_polymorphic_pconstant (cst,u) env =
  if not (Univ.Instance.is_empty u) then false
  else template_polymorphic_constant cst env

let lookup_projection cst env =
  match (lookup_constant (Projection.constant cst) env).const_proj with 
  | Some pb -> pb
  | None -> anomaly (Pp.str "lookup_projection: constant is not a projection")

let is_projection cst env =
  match (lookup_constant cst env).const_proj with 
  | Some _ -> true
  | None -> false

(* Mutual Inductives *)
let lookup_mind = lookup_mind

let polymorphic_ind (mind,i) env =
  (lookup_mind mind env).mind_polymorphic

let polymorphic_pind (ind,u) env =
  if Univ.Instance.is_empty u then false
  else polymorphic_ind ind env

let type_in_type_ind (mind,i) env =
  not (lookup_mind mind env).mind_typing_flags.check_universes

let template_polymorphic_ind (mind,i) env =
  match (lookup_mind mind env).mind_packets.(i).mind_arity with 
  | TemplateArity _ -> true
  | RegularArity _ -> false

let template_polymorphic_pind (ind,u) env =
  if not (Univ.Instance.is_empty u) then false
  else template_polymorphic_ind ind env
  
let add_mind_key kn mind_key env =
  let new_inds = Mindmap_env.add kn mind_key env.env_globals.env_inductives in
  let new_globals =
    { env.env_globals with
	env_inductives = new_inds } in
  { env with env_globals = new_globals }

let add_mind kn mib env =
  let li = ref no_link_info in add_mind_key kn (mib, li) env

(* Lookup of section variables *)

let lookup_constant_variables c env =
  let cmap = lookup_constant c env in
  Context.Named.to_vars cmap.const_hyps

let lookup_inductive_variables (kn,i) env =
  let mis = lookup_mind kn env in
  Context.Named.to_vars mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Returns the list of global variables in a term *)

let vars_of_global env constr =
  match kind_of_term constr with
      Var id -> Id.Set.singleton id
    | Const (kn, _) -> lookup_constant_variables kn env
    | Ind (ind, _) -> lookup_inductive_variables ind env
    | Construct (cstr, _) -> lookup_constructor_variables cstr env
    (** FIXME: is Proj missing? *)
    | _ -> raise Not_found

let global_vars_set env constr =
  let rec filtrec acc c =
    let acc =
      match kind_of_term c with
      | Var _ | Const _ | Ind _ | Construct _ ->
	  Id.Set.union (vars_of_global env c) acc
      | _ ->
	  acc in
    fold_constr filtrec acc c
  in
    filtrec Id.Set.empty constr


(* [keep_hyps env ids] keeps the part of the section context of [env] which
   contains the variables of the set [ids], and recursively the variables
   contained in the types of the needed variables. *)

let really_needed env needed =
  Context.Named.fold_inside
    (fun need decl ->
      if Id.Set.mem (get_id decl) need then
        let globc =
          match decl with
            | LocalAssum _ -> Id.Set.empty
            | LocalDef (_,c,_) -> global_vars_set env c in
        Id.Set.union
          (global_vars_set env (get_type decl))
          (Id.Set.union globc need)
      else need)
    ~init:needed
    (named_context env)

let keep_hyps env needed =
  let really_needed = really_needed env needed in
  Context.Named.fold_outside
    (fun d nsign ->
      if Id.Set.mem (get_id d) really_needed then Context.Named.add d nsign
      else nsign)
    (named_context env)
    ~init:empty_named_context

(* Modules *)

let add_modtype mtb env =
  let mp = mtb.mod_mp in
  let new_modtypes = MPmap.add mp mtb env.env_globals.env_modtypes in
  let new_globals = { env.env_globals with env_modtypes = new_modtypes } in
  { env with env_globals = new_globals }

let shallow_add_module mb env =
  let mp = mb.mod_mp in
  let new_mods = MPmap.add mp mb env.env_globals.env_modules in
  let new_globals = { env.env_globals with env_modules = new_mods } in
  { env with env_globals = new_globals }

let lookup_module mp env =
    MPmap.find mp env.env_globals.env_modules


let lookup_modtype mp env = 
  MPmap.find mp env.env_globals.env_modtypes

(*s Judgments. *)

type unsafe_judgment = {
  uj_val : constr;
  uj_type : types }

let make_judge v tj =
  { uj_val = v;
    uj_type = tj }

let j_val j = j.uj_val
let j_type j = j.uj_type

type unsafe_type_judgment = {
  utj_val : constr;
  utj_type : sorts }

(*s Compilation of global declaration *)

let compile_constant_body = Cbytegen.compile_constant_body false

exception Hyp_not_found

let apply_to_hyp ctxt id f =
  let rec aux rtail ctxt =
    match match_named_context_val ctxt with
    | Some (d, v, ctxt) ->
	if Id.equal (get_id d) id then
          push_named_context_val_val (f ctxt.env_named_ctx d rtail) v ctxt
	else
	  let ctxt' = aux (d::rtail) ctxt in
	  push_named_context_val_val d v ctxt'
    | None -> raise Hyp_not_found
  in aux [] ctxt

(* To be used in Logic.clear_hyps *)
let remove_hyps ids check_context check_value ctxt =
  let rec remove_hyps ctxt = match match_named_context_val ctxt with
  | None -> empty_named_context_val, false
  | Some (d, v, rctxt) ->
    let (ans, seen) = remove_hyps rctxt in
    if Id.Set.mem (get_id d) ids then (ans, true)
    else if not seen then ctxt, false
    else
      let rctxt' = ans in
      let d' = check_context d in
      let v' = check_value v in
      if d == d' && v == v' && rctxt == rctxt' then
        ctxt, true
      else push_named_context_val_val d' v' rctxt', true
  in
  fst (remove_hyps ctxt)

(*spiwack: the following functions assemble the pieces of the retroknowledge
   note that the "consistent" register function is available in the module
   Safetyping, Environ only synchronizes the proactive and the reactive parts*)

open Retroknowledge

(* lifting of the "get" functions works also for "mem"*)
let retroknowledge f env =
  f env.retroknowledge

let registered env field =
    retroknowledge mem env field

let register_one env field entry =
  { env with retroknowledge = Retroknowledge.add_field env.retroknowledge field entry }

(* [register env field entry] may register several fields when needed *)
let register env field entry =
  match field with
    | KInt31 (grp, Int31Type) ->
        let i31c = match kind_of_term entry with
                     | Ind i31t -> mkConstructUi (i31t, 1)
		     | _ -> anomaly ~label:"Environ.register" (Pp.str "should be an inductive type")
	in
        register_one (register_one env (KInt31 (grp,Int31Constructor)) i31c) field entry
    | field -> register_one env field entry

(* the Environ.register function syncrhonizes the proactive and reactive
   retroknowledge. *)
let dispatch =

  (* subfunction used for static decompilation of int31 (after a vm_compute,
     see pretyping/vnorm.ml for more information) *)
  let constr_of_int31 =
    let nth_digit_plus_one i n = (* calculates the nth (starting with 0)
                                    digit of i and adds 1 to it
                                    (nth_digit_plus_one 1 3 = 2) *)
      if Int.equal (i land (1 lsl n)) 0 then
        1
      else
        2
    in
      fun ind -> fun digit_ind -> fun tag ->
	let array_of_int i =
	  Array.init 31 (fun n -> mkConstruct
			   (digit_ind, nth_digit_plus_one i (30-n)))
	in
	(* We check that no bit above 31 is set to one. This assertion used to
	fail in the VM, and led to conversion tests failing at Qed. *)
        assert (Int.equal (tag lsr 31) 0);
	mkApp(mkConstruct(ind, 1), array_of_int tag)
  in

  (* subfunction which dispatches the compiling information of an
     int31 operation which has a specific vm instruction (associates
     it to the name of the coq definition in the reactive retroknowledge) *)
  let int31_op n op prim kn =
    { empty_reactive_info with
      vm_compiling = Some (Cbytegen.op_compilation n op kn);
      native_compiling = Some (Nativelambda.compile_prim prim (Univ.out_punivs kn));
    }
  in

fun rk value field ->
  (* subfunction which shortens the (very common) dispatch of operations *)
  let int31_op_from_const n op prim =
    match kind_of_term value with
      | Const kn ->  int31_op n op prim kn
      | _ -> anomaly ~label:"Environ.register" (Pp.str "should be a constant")
  in
  let int31_binop_from_const op prim = int31_op_from_const 2 op prim in
  let int31_unop_from_const op prim = int31_op_from_const 1 op prim in
  match field with
    | KInt31 (grp, Int31Type) ->
        let int31bit =
          (* invariant : the type of bits is registered, otherwise the function
             would raise Not_found. The invariant is enforced in safe_typing.ml *)
          match field with
          | KInt31 (grp, Int31Type) -> Retroknowledge.find rk (KInt31 (grp,Int31Bits))
          | _ -> anomaly ~label:"Environ.register"
              (Pp.str "add_int31_decompilation_from_type called with an abnormal field")
        in
        let i31bit_type =
          match kind_of_term int31bit with
          | Ind (i31bit_type,_) -> i31bit_type
          |  _ -> anomaly ~label:"Environ.register"
              (Pp.str "Int31Bits should be an inductive type")
        in
        let int31_decompilation =
          match kind_of_term value with
          | Ind (i31t,_) ->
              constr_of_int31 i31t i31bit_type
          | _ -> anomaly ~label:"Environ.register"
              (Pp.str "should be an inductive type")
        in
        { empty_reactive_info with
          vm_decompile_const = Some int31_decompilation;
          vm_before_match = Some Cbytegen.int31_escape_before_match;
          native_before_match = Some (Nativelambda.before_match_int31 i31bit_type);
        }
    | KInt31 (_, Int31Constructor) ->
        { empty_reactive_info with
          vm_constant_static = Some Cbytegen.compile_structured_int31;
          vm_constant_dynamic = Some Cbytegen.dynamic_int31_compilation;
          native_constant_static = Some Nativelambda.compile_static_int31;
          native_constant_dynamic = Some Nativelambda.compile_dynamic_int31;
        }
    | KInt31 (_, Int31Plus) -> int31_binop_from_const Cbytecodes.Kaddint31
							  Primitives.Int31add
    | KInt31 (_, Int31PlusC) -> int31_binop_from_const Cbytecodes.Kaddcint31
							   Primitives.Int31addc
    | KInt31 (_, Int31PlusCarryC) -> int31_binop_from_const Cbytecodes.Kaddcarrycint31
								Primitives.Int31addcarryc
    | KInt31 (_, Int31Minus) -> int31_binop_from_const Cbytecodes.Ksubint31
							   Primitives.Int31sub
    | KInt31 (_, Int31MinusC) -> int31_binop_from_const Cbytecodes.Ksubcint31
							    Primitives.Int31subc
    | KInt31 (_, Int31MinusCarryC) -> int31_binop_from_const
	                                Cbytecodes.Ksubcarrycint31 Primitives.Int31subcarryc
    | KInt31 (_, Int31Times) -> int31_binop_from_const Cbytecodes.Kmulint31
							   Primitives.Int31mul
    | KInt31 (_, Int31TimesC) -> int31_binop_from_const Cbytecodes.Kmulcint31
							   Primitives.Int31mulc
    | KInt31 (_, Int31Div21) -> int31_op_from_const 3 Cbytecodes.Kdiv21int31
                                                           Primitives.Int31div21
    | KInt31 (_, Int31Diveucl) -> int31_binop_from_const Cbytecodes.Kdivint31
							 Primitives.Int31diveucl
    | KInt31 (_, Int31AddMulDiv) -> int31_op_from_const 3 Cbytecodes.Kaddmuldivint31
                                                         Primitives.Int31addmuldiv
    | KInt31 (_, Int31Compare) -> int31_binop_from_const Cbytecodes.Kcompareint31
							     Primitives.Int31compare
    | KInt31 (_, Int31Head0) -> int31_unop_from_const Cbytecodes.Khead0int31
							  Primitives.Int31head0
    | KInt31 (_, Int31Tail0) -> int31_unop_from_const Cbytecodes.Ktail0int31
							  Primitives.Int31tail0
    | KInt31 (_, Int31Lor) -> int31_binop_from_const Cbytecodes.Klorint31
							 Primitives.Int31lor
    | KInt31 (_, Int31Land) -> int31_binop_from_const Cbytecodes.Klandint31
							  Primitives.Int31land
    | KInt31 (_, Int31Lxor) -> int31_binop_from_const Cbytecodes.Klxorint31
							  Primitives.Int31lxor
    | _ -> empty_reactive_info

let _ = Hook.set Retroknowledge.dispatch_hook dispatch
