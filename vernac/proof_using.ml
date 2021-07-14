(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open Util
open Vernacexpr
open Context.Named.Declaration

module SectionDecl = Context.Section.Declaration

let known_names = Summary.ref [] ~name:"proofusing-nameset"

module USet = Cset

let deps env cst = global_section_set env (Constr.mkConst cst)
(*
let deps_id env id = deps env (Environ.section_full_name id env)
let deps_vars env cst = global_vars_set env (Constr.mkConst cst)
*)
let really_needed env csts = Cset.fold (fun cst -> Cset.union (deps env cst)) csts Cset.empty
(*
let deps_vars_id env id = deps_vars env (Environ.section_full_name id env)
let really_needed_id env ids = Id.Set.fold (fun id -> Id.Set.union (deps_vars_id env id)) ids Id.Set.empty
*)

let rec close_fwd env s =
  let s' =
    List.fold_left (fun s decl ->
      let vbty = deps env (SectionDecl.get_section_decl_name decl) in
      if USet.exists (fun v -> USet.mem v s) vbty
      then USet.add (SectionDecl.get_section_decl_name decl) (USet.union s vbty) else s)
    s (section_context env)
    in
  if USet.equal s s' then s else close_fwd env s'

let set_of_type env ty =
  List.fold_left (fun acc ty ->
      USet.union (global_section_set env ty) acc)
    USet.empty ty

let full_set env =
  List.fold_right (fun d -> USet.add (SectionDecl.get_section_decl_name d))
    (section_context env) USet.empty

let process_expr env e v_ty =
  let rec aux = function
    | SsEmpty -> USet.empty
    | SsType -> v_ty
    | SsSingl { CAst.v = id } -> set_of_id id
    | SsUnion(e1,e2) -> USet.union (aux e1) (aux e2)
    | SsSubstr(e1,e2) -> USet.diff (aux e1) (aux e2)
    | SsCompl e -> USet.diff (full_set env) (aux e)
    | SsFwdClose e -> close_fwd env (aux e)
  and set_of_id id =
    if Id.to_string id = "All" then
      full_set env
    else if CList.mem_assoc_f Id.equal id !known_names then
      aux (CList.assoc_f Id.equal id !known_names)
    else USet.singleton (section_full_name id env)
  in
  aux e

let process_expr env e ty =
  let v_ty = set_of_type env ty in
  let s = USet.union v_ty (process_expr env e v_ty) in
  USet.elements s

type t = Names.Cset.t

let definition_using env evd ~using ~terms =
  let terms = List.map (EConstr.to_constr evd) terms in
  let l = process_expr env using terms in
  USet.(List.fold_right add l empty)

let name_set id expr = known_names := (id,expr) :: !known_names

(*
let really_needed_cst env needed =
  let open! Context.Named.Declaration in
  Context.Named.fold_inside
    (fun need cst ->
      if Cset.mem cst need then
        let globc =
          match decl with
            | LocalAssum _ -> Cset.empty
            | LocalDef (_,c,_) -> global_section_set env c in
        Cset.union
          (global_section_set env (mkConst cst))
          (Cset.union globc need)
      else need)
    ~init:needed
    (named_context env)

let really_needed env needed =
  let open! Context.Named.Declaration in
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
*)

let keep_ordered_hyps env needed =
  let open Context.Section.Declaration in
  List.fold_right
    (fun d nsign ->
      let cst = get_section_decl_name d in
      if Cset.mem cst needed then cst :: nsign
      else nsign)
    (section_context env)
    []

let compute_used_variables env using =
  let open Context.Section.Declaration in
  let aux entry ctx =
    match entry with
    | SectionAssum _ -> ctx
    | SectionDef ({Context.binder_name=x},bo, ty) ->
       let x = get_section_decl_name entry in
       if Cset.mem x ctx || not (Cset.subset (deps env x) ctx) then ctx
       else Cset.add x ctx in
       List.fold_right aux (section_context env) using

let minimize_hyps env ids =
  let rec aux ids =
    let ids' =
      Cset.fold (fun cst alive ->
        let impl_by_id = Cset.remove cst (deps env cst) in
        if Cset.is_empty impl_by_id then alive
        else Cset.diff alive impl_by_id)
      ids ids in
    if Cset.equal ids ids' then ids else aux ids'
  in
    aux ids


let remove_ids_and_lets env s csts =
  let open Context.Section.Declaration in
  let not_ids cst = not (Cset.mem cst csts) in
  let no_body cst = is_section_assum (Context.Section.lookup (Constant.basename cst) (section_context env)) in
  Cset.filter (fun id ->
      not_ids id &&
     (no_body id ||
       Cset.exists not_ids (Cset.filter no_body (deps env id)))) s

let record_proof_using expr =
  Aux_file.record_in_aux "suggest_proof_using" expr

let debug_proof_using = CDebug.create ~name:"proof-using" ()

(* Variables in [skip] come from after the definition, so don't count
   for "All". Used in the variable case since the env contains the
   variable itself. *)
let suggest_common env ppid used ids_typ skip =
  let module S = Cset in
  let open Pp in
  let pr_set parens s =
    let pr cst = Id.print (Constant.basename cst) in
    let wrap ppcmds =
      if parens && S.cardinal s > 1 then str "(" ++ ppcmds ++ str ")"
      else ppcmds in
    wrap (prlist_with_sep (fun _ -> str" ") pr (S.elements s)) in

  let needed = minimize_hyps env (remove_ids_and_lets env used ids_typ) in
  let all_needed = really_needed env needed in
  let all = full_set env in
  let all = S.diff all skip in
  let fwd_typ = close_fwd env ids_typ in
  let () = debug_proof_using (fun () ->
      str "All "        ++ pr_set false all ++ fnl() ++
      str "Type "       ++ pr_set false ids_typ ++ fnl() ++
      str "needed "     ++ pr_set false needed ++ fnl() ++
      str "all_needed " ++ pr_set false all_needed ++ fnl() ++
      str "Type* "      ++ pr_set false fwd_typ)
  in
  let valid_exprs = ref [] in
  let valid e = valid_exprs := e :: !valid_exprs in
  if S.is_empty needed then valid (str "Type");
  if S.equal all_needed fwd_typ then valid (str "Type*");
  if S.equal all all_needed then valid(str "All");
  valid (pr_set false needed);
  Feedback.msg_info (
    str"The proof of "++ ppid ++ spc() ++
    str "should start with one of the following commands:"++spc()++
    v 0 (
    prlist_with_sep cut (fun x->str"Proof using " ++x++ str". ") !valid_exprs));
  if Aux_file.recording ()
  then
    let s = string_of_ppcmds (prlist_with_sep (fun _ -> str";")  (fun x->x) !valid_exprs) in
    record_proof_using s

let suggest_proof_using = ref false

let () =
  Goptions.(declare_bool_option
    { optdepr  = false;
      optkey   = ["Suggest";"Proof";"Using"];
      optread  = (fun () -> !suggest_proof_using);
      optwrite = ((:=) suggest_proof_using) })

let suggest_constant env kn =
  if !suggest_proof_using
  then begin
    let open Declarations in
    let body = lookup_constant kn env in
    let used = USet.of_list @@ body.const_hyps in
    let ids_typ = global_section_set env body.const_type in
    suggest_common env (Printer.pr_constant env kn) used ids_typ USet.empty
  end

let suggest_variable env id =
  if !suggest_proof_using
  then begin
    match lookup_named id env with
    | LocalDef (_,body,typ) ->
      let ids_typ = global_section_set env typ in
      let ids_body = global_section_set env body in
      let used = USet.union ids_body ids_typ in
      suggest_common env (Id.print id) used ids_typ (USet.singleton (section_full_name id env))
    | LocalAssum _ -> assert false
  end

let value = ref None

let using_to_string us = Pp.string_of_ppcmds (Ppvernac.pr_using us)
let using_from_string us = Pcoq.Entry.parse G_vernac.section_subset_expr (Pcoq.Parsable.make (Stream.of_string us))

let proof_using_opt_name = ["Default";"Proof";"Using"]
let () =
  Goptions.(declare_stringopt_option
    { optdepr  = false;
      optkey   = proof_using_opt_name;
      optread  = (fun () -> Option.map using_to_string !value);
      optwrite = (fun b -> value := Option.map using_from_string b);
    })

let get_default_proof_using () = !value
