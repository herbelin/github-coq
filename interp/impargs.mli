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
open EConstr
open Environ

(** {6 Implicit Arguments } *)
(** Here we store the implicit arguments. Notice that we
    are outside the kernel, which knows nothing about implicit arguments. *)

val make_implicit_args : bool -> unit
val make_strict_implicit_args : bool -> unit
val make_strongly_strict_implicit_args : bool -> unit
val make_reversible_pattern_implicit_args : bool -> unit
val make_contextual_implicit_args : bool -> unit
val make_maximal_implicit_args : bool -> unit

val is_implicit_args : unit -> bool
val is_strict_implicit_args : unit -> bool
val is_strongly_strict_implicit_args : unit -> bool
val is_reversible_pattern_implicit_args : unit -> bool
val is_contextual_implicit_args : unit -> bool
val is_maximal_implicit_args : unit -> bool

val with_implicit_protection : ('a -> 'b) -> 'a -> 'b

(** {6 Data types. } *)

(** An [implicits_list] is a list of positions telling which arguments
    of a reference can be automatically inferred *)

type dependency_explanation
type argument_status = Name.t * int option * dependency_explanation

type implicit_proper_status
type implicit_status = argument_status * implicit_proper_status option
  (** [None] = Not implicit; let-in skipped *)

type implicit_side_condition
type implicits_list = implicit_side_condition * implicit_status list

(** {6 Implicit arguments lists. } *)

val default_dependency_explanation : dependency_explanation
val default_implicit : maximal:bool -> force:bool -> implicit_proper_status
  (** maximal:true = maximal contextual insertion
      force:true = always infer, never turn into evar/subgoal *)

val is_status_implicit : implicit_status -> bool
val binding_kind_of_status : implicit_status -> Glob_term.binding_kind
val is_inferable_implicit : bool -> int -> implicit_status -> bool
val name_of_argument : int -> implicit_status -> Id.t
val match_argument : int -> implicit_status -> Constrexpr.explicitation -> bool
val maximal_insertion_of : implicit_status -> bool
val force_inference_of : implicit_status -> bool
val is_named_argument : Id.t -> implicit_status list -> bool
val is_nondep_argument : int -> implicit_status list -> bool
val explicitation : implicit_status -> Constrexpr.explicitation
val print_allowed_named_implicit : implicit_status list -> Pp.t
val print_allowed_nondep_implicit : implicit_status list -> Pp.t

(** {6 Name of arguments. } *)

val compute_argument_names : env -> Evd.evar_map -> types -> Name.t list
  (** compute argument names as done for implicit arguments *)

(** {6 Setting auto+manual implicit arguments (done using the global environment). } *)

type manual_implicits = (Name.t * bool) option CAst.t list

val compute_implicits_with_manual : env -> Evd.evar_map -> types ->
  manual_implicits -> implicit_status list
  (** compute auto+manual implicit arguments associated to a type *)

type mib_manual_implicits = (manual_implicits * manual_implicits list) list

val declare_var_implicits : variable ->
  impl:Glob_term.binding_kind -> impargs:manual_implicits option -> unit
val declare_constant_implicits : Constant.t -> impargs:manual_implicits option -> unit
val declare_mib_implicits : MutInd.t -> impargs:mib_manual_implicits -> unit
  (** compute auto+manual implicit arguments associated to a global reference *)

val implicits_of_global : GlobRef.t -> implicits_list list

val projection_implicits : env -> Projection.t -> implicit_status list ->
  implicit_status list
[@@ocaml.deprecated "please report if used"]

(** {6 Setting auto implicit arguments} *)

val set_auto_implicits : bool -> GlobRef.t -> unit

(** {6 Setting manual implicit arguments} *)

(** [set_manual_implicits local ref l]
   Manual declaration of implicit arguments.
  [l] is a list of possible sequences of implicit statuses. *)
val set_manual_implicits : bool -> GlobRef.t -> (Name.t * Glob_term.binding_kind) list list -> unit

(** {6 Multiple implicit arguments *)

val extract_impargs_data :
  implicits_list list -> ((int * int) option * implicit_status list) list

val make_implicits_list : implicit_status list -> implicits_list list

val drop_first_implicits : int -> implicits_list -> implicits_list

val select_impargs_size : int -> implicits_list list -> implicit_status list

val select_stronger_impargs : implicits_list list -> implicit_status list

val select_impargs_size_for_proj :
  nexpectedparams:int -> ngivenparams:int -> nextraargs:int ->
  implicits_list list -> (implicit_status list * implicit_status list, int list Lazy.t) Util.union

val impargs_for_proj :
  nexpectedparams:int -> nextraargs:int ->
  implicit_status list -> implicit_status list * implicit_status list
