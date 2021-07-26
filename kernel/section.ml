(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Univ
open Declarations

(*
module SectionDecl = Context.Section.Declaration

type persistence_flag = bool
*)

type section_entry =
| SecDefinition of persistence_flag * Constant.t * constant_body
| SecInductive of MutInd.t * mutual_inductive_body

type 'a t = {
  prev : 'a t option;
  (** Section surrounding the current one *)
  entries : section_entry list;
  (** Global declarations introduced in the section *)
  context : Constr.named_context;
  (** Declarations local to the section, intended to be interleaved
      with global declarations *)
  mono_universes : ContextSet.t;
  (** Global universes introduced in the section *)
  poly_universes : UContext.t;
  (** Universes local to the section *)
  all_poly_univs : UContext.t;
  (** All polymorphic universes, including from previous sections. *)
  has_poly_univs : bool;
  (** Are there polymorphic universes or constraints, including in previous sections. *)
  expand_info_map : expand_info;
  (** Tells how to re-instantiate global declarations when they are
      generalized *)
  cooking_info_map : cooking_info entry_map;
  custom : 'a;
}

let has_poly_univs sec = sec.has_poly_univs

let rec depth = function
  | None -> 0
  | Some sec -> 1 + depth sec.prev

let rec polymorphic_universes = function
  | None -> []
  | Some sec -> sec.poly_universes :: polymorphic_universes sec.prev

(*
let all_poly_univs sec = sec.all_poly_univs
*)

let map_custom f sec = {sec with custom = f sec.custom}

let add_emap e v (cmap, imap) = match e with
| SecDefinition (con,_) -> (Cmap.add con v cmap, imap)
| SecInductive (ind,_) -> (cmap, Mindmap.add ind v imap)


let poly_universes sec = sec.poly_universes

let push_local_universe_context ctx sec =
  if UContext.is_empty ctx then sec
  else
    let sctx = sec.poly_universes in
    let poly_universes = UContext.union sctx ctx in
    let all_poly_univs = UContext.union sec.all_poly_univs ctx in
    { sec with poly_universes; all_poly_univs; has_poly_univs = true }

let rec is_polymorphic_univ u sec =
  let uctx = sec.poly_universes in
  let here = Array.exists (fun u' -> Level.equal u u') (Instance.to_array (UContext.instance uctx)) in
  here || Option.cata (is_polymorphic_univ u) false sec.prev

let push_constraints uctx sec =
  if sec.has_poly_univs &&
     Constraints.exists
       (fun (l,_,r) -> is_polymorphic_univ l sec || is_polymorphic_univ r sec)
       (snd uctx)
  then CErrors.user_err
      Pp.(str "Cannot add monomorphic constraints which refer to section polymorphic universes.");
  let uctx' = sec.mono_universes in
  let mono_universes =  (ContextSet.union uctx uctx') in
  { sec with mono_universes }

let open_section ~custom prev =
  {
    prev;
    context = [];
    mono_universes = ContextSet.empty;
    poly_universes = UContext.empty;
    all_poly_univs = Option.cata (fun sec -> sec.all_poly_univs) Univ.UContext.empty prev;
    has_poly_univs = Option.cata has_poly_univs false prev;
    entries = [];
    expand_info_map = (Cmap.empty, Mindmap.empty);
    cooking_info_map = (Cmap.empty, Mindmap.empty);
    custom = custom;
  }

let close_section sec =
  sec.prev, sec.entries, sec.mono_universes, sec.custom

let push_local d sec =
  { sec with context = d :: sec.context }

let extract_hyps vars used =
  (* Only keep the part that is used by the declaration *)
  List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) used) vars

let segment_of_entry e uctx sec =
  let hyps = match e with
  | SecDefinition (_con, body) -> body.Declarations.const_hyps
  | SecInductive (_mind, mib) -> mib.Declarations.mind_hyps
  in
  let hyps = Context.Named.to_vars hyps in
  (* [sec.context] are the named hypotheses, [hyps] the subset that is
     declared by the global *)
  let ctx = extract_hyps sec.context hyps in
  Cooking.make_cooking_info sec.expand_info_map ctx uctx

let push_global ~poly e sec =
  if has_poly_univs sec && not poly
  then CErrors.user_err
      Pp.(str "Cannot add a universe monomorphic declaration when \
               section polymorphic universes are present.")
  else
    let cooking_info = segment_of_entry e sec.poly_universes sec in
    let cooking_info_map = add_emap e cooking_info sec.cooking_info_map in
    let expand_info_map = add_emap e cooking_info.abstr_inst_info sec.expand_info_map in
    { sec with entries = e :: sec.entries; expand_info_map; cooking_info_map }

let segment_of_constant con sec = Cmap.find con (fst sec.cooking_info_map)
let segment_of_inductive con sec = Mindmap.find con (snd sec.cooking_info_map)

let extract_hyps vars used =
  (* Only keep the part that is used by the declaration *)
  let vars1,vars2 = List.partition (fun decl -> Cset.mem (SectionDecl.get_section_decl_name decl) used) vars in
  vars1, List.map SectionDecl.get_section_decl_name vars2

let section_segment_of_entry vars hyps uctx =
  let uctx, abstr_further_univctx = match uctx with
    | a::l -> a, l
    | _ -> CErrors.anomaly (Pp.str "Ill-formed universe section segment.") in
  (* [vars] are the named hypotheses, [hyps] the subset that is declared by the
     global *)
  let hyps, abstr_further_ctx = extract_hyps vars (Cset.of_list hyps) in
  let inst, auctx = Univ.abstract_universes uctx in
  {
    abstr_ctx = hyps;
    abstr_subst = inst;
    abstr_uctx = auctx;
    abstr_further_ctx;
    abstr_further_univctx;
  }

(*
let empty_segment = {
  expand_info = (Cmap.empty, Mindmap.empty);
  abstr_info = {
      abstr_ctx = [];
      abstr_subst = [];
      abstr_uctx = AbstractContext.empty;
      abstr_usubst = Level.Map.empty;
    };
  abstr_inst_info = {
      abstr_inst = [||];
      abstr_uinst = Univ.Instance.empty;
    };
  names_info = Id.Set.empty;
}

let is_in_section _env gr sec =
  let open GlobRef in
  match gr with
  | VarRef id ->
    let vars = sec.context in
    List.exists (fun decl -> Id.equal id (NamedDecl.get_id decl)) vars
  | ConstRef con ->
    Cmap.mem con (fst sec.expand_info_map)
  | IndRef (ind, _) | ConstructRef ((ind, _), _) ->
    Mindmap.mem ind (snd sec.expand_info_map)

let get_section_assum_name = function
  | SectionAssum (cst,_) -> Some cst.Context.binder_name
  | SectionDef _ -> None

let is_in_section env gr sec =
  let open GlobRef in
  match gr with
  | VarRef id ->
    let vars = Environ.section_context env in
    List.exists (fun decl -> Id.equal id (Constant.basename (get_section_decl_name decl))) vars
  | ConstRef con ->
    Cmap.mem con (fst sec.expand_info_map)
  | IndRef (ind, _) | ConstructRef ((ind, _), _) ->
    Mindmap.mem ind (snd sec.expand_info_map)
*)

let section_decl_of_const_body cst cb =
  match cb.const_body with
  | Undef _ -> SectionDecl.SectionAssum (Context.make_annot cst cb.const_relevance, cb.const_type)
  | Def c -> SectionDecl.SectionDef (Context.make_annot cst cb.const_relevance, c, cb.const_type)
  | OpaqueDef _ -> CErrors.user_err Pp.(strbrk "Opaque local definition not supported.")
  | Primitive _ -> assert false (* forbidden in add_possible_retroknowledge *)

let is_const_in_section cst sec = Cset.mem cst sec.const_cache
let is_mind_in_section mind sec = Mindset.mem mind sec.mind_cache

let is_local_in_section gr sec =
  match gr with
  | GlobRef.ConstRef cst -> not (is_const_in_section cst sec)
  | _ -> false

let is_persistent_in_section gr sec =
  let open GlobRef in
  match gr with
  | VarRef _id -> assert false
  | ConstRef cst -> is_const_in_section cst sec
  | IndRef (mind, _) | ConstructRef ((mind, _), _) -> is_mind_in_section mind sec
