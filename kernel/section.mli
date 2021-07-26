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
open Univ

(** Kernel implementation of sections. *)

type 'a t
(** Type of sections with additional data ['a] *)

val depth : 'a t option -> int
(** Number of nested sections (None = 0). *)

val map_custom : ('a -> 'a) -> 'a t -> 'a t
(** Modify the custom data *)

(** {6 Manipulating sections} *)

type persistence_flag = bool

type section_entry =
| SecDefinition of persistence_flag * Constant.t * Declarations.constant_body
| SecInductive of MutInd.t * Declarations.mutual_inductive_body

val open_section : custom:'a -> 'a t option -> 'a t
(** Open a new section with the provided universe polymorphic status. Sections
    can be nested, with the proviso that polymorphic sections cannot appear
    inside a monomorphic one. *)

val close_section : 'a t -> 'a t option * section_entry list * ContextSet.t * 'a
(** Close the current section and returns the entries defined inside, the set
    of global monomorphic constraints added in this section *)

(** {6 Extending sections} *)

val push_local : Constr.named_declaration -> 'a t -> 'a t
(** Extend the current section with a local definition (cf. push_named). *)

val push_local_universe_context : UContext.t -> 'a t -> 'a t
(** Extend the current section with a local universe context. Assumes that the
    last opened section is polymorphic. *)

val push_constraints : ContextSet.t -> 'a t -> 'a t
(** Extend the current section with a global universe context.
    Assumes that the last opened section is monomorphic. *)

val push_field : poly:bool -> section_entry -> 'a t -> 'a t
(** Make the field as having been defined in this section. *)

(** {6 Retrieving section data} *)

val poly_universes : 'a t -> UContext.t
(** Returns polymorphic universes of the current section *)

val polymorphic_universes : 'a t option -> UContext.t list

(*
val all_poly_univs : 'a t -> Univ.Level.t array
(** Returns all polymorphic universes, including those from previous
   sections. Earlier sections are earlier in the array.

    NB: even if the array is empty there may be polymorphic
   constraints about monomorphic universes, which prevent declaring
   monomorphic globals. *)
*)

val empty_segment : Declarations.cooking_info
(** Nothing to abstract *)

val section_segment_of_entry : Constr.section_declaration list
  -> Constant.t list -> Univ.UContext.t list -> Declarations.abstr_info

val segment_of_constant : Constant.t -> 'a t -> Declarations.cooking_info
(** Section segment at the time of the constant declaration *)

val segment_of_inductive : MutInd.t -> 'a t -> Declarations.cooking_info
(** Section segment at the time of the inductive declaration *)
(*
val is_in_section : Environ.env -> GlobRef.t -> 'a t -> bool
*)
val is_persistent_in_section : GlobRef.t -> 'a t -> bool
(** Tell if a reference is persistent in the section *)

val is_local_in_section : GlobRef.t -> 'a t -> bool
(** Tell if a reference is non persistent in the section *)
