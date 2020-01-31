(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Notation_term
open Glob_term

(** {5 Utilities about [notation_constr]} *)

val eq_notation_constr : Id.t list * Id.t list -> notation_constr -> notation_constr -> bool

(** Substitution of kernel names in interpretation data                *)

val subst_interpretation :
  Mod_subst.substitution -> interpretation -> interpretation

(** Name of the special identifier used to encode recursive notations  *)

val ldots_var : Id.t

(** {5 Translation back and forth between [glob_constr] and [notation_constr]} *)

(** Translate a [glob_constr] into a notation given the list of variables
    bound by the notation; also interpret recursive patterns           *)

val notation_constr_of_glob_constr : notation_interp_env ->
  glob_constr -> notation_constr * reversibility_status

(** Re-interpret a notation as a [glob_constr], taking care of binders *)

val apply_cases_pattern : ?loc:Loc.t ->
  (Id.t list * cases_pattern_disjunction) * Id.t -> glob_constr -> glob_constr

val glob_constr_of_notation_constr_with_binders : ?loc:Loc.t ->
  ('a -> Name.t -> 'a * ((Id.t list * cases_pattern_disjunction) * Id.t) option * Name.t) ->
  ('a -> notation_constr -> glob_constr) ->
  'a -> notation_constr -> glob_constr

val glob_constr_of_notation_constr : ?loc:Loc.t -> notation_constr -> glob_constr

(** {5 Matching a notation pattern against a [glob_constr]} *)

(** [match_notation_constr] matches a [glob_constr] against a notation
    interpretation; raise [No_match] if the matching fails   *)

exception No_match

val match_notation_constr : bool -> 'a glob_constr_g -> interpretation ->
      ('a glob_constr_g * extended_subscopes) list * ('a glob_constr_g list * extended_subscopes) list *
      ('a cases_pattern_disjunction_g * extended_subscopes) list *
      ('a extended_glob_local_binder_g list * extended_subscopes) list

val match_notation_constr_cases_pattern :
  'a cases_pattern_g -> interpretation ->
  (('a cases_pattern_g * extended_subscopes) list * ('a cases_pattern_g list * extended_subscopes) list) *
    (int * 'a cases_pattern_g list)

val match_notation_constr_ind_pattern :
  inductive -> 'a cases_pattern_g list -> interpretation ->
  (('a cases_pattern_g * extended_subscopes) list * ('a cases_pattern_g list * extended_subscopes) list) *
    (int * 'a cases_pattern_g list)

(** {5 Manipulating notation strings } *)

(** Building notation key *)

type symbol =
  | Terminal of string              (* an expression including symbols or a simply-quoted ident, e.g. "'U'" or "!" *)
  | NonTerminal of Id.t             (* an identifier "x" *)
  | SProdList of Id.t * symbol list (* an expression "x sep .. sep y", remembering x (or y) and sep *)
  | Break of int                    (* a sequence of blanks > 1, e.g. "   " *)

val symbol_eq : symbol -> symbol -> bool

(** Encode/decode notation under a string form "_ U _"
    Note: [Break] markers are dropped *)
val make_notation_key : Constrexpr.notation_entry_level -> symbol list -> Constrexpr.notation
val decompose_notation_key : Constrexpr.notation -> Constrexpr.notation_entry_level * symbol list

(** Decompose a notation of the form "a 'U' b"
    Returning the pairs of recursive variables and the list of non-recursive variables
    If not [onlyprint], variables have to be distinct *)
val analyze_notation_tokens : onlyprint:bool -> string -> (Id.t * Id.t) list * Id.t list * symbol list

(** This collects the possible interpretations of a notation string
    depending on whether it is in "x 'U' y" or "_ U _" format;
    resulting in a key where variables are replaced by "_" and quotes are dropped *)
val interp_notation_string : string -> string list

(** This tells if a notation string (or component of a string) refers to a given notation *)
val find_notation_string : allow_part:bool -> Constrexpr.notation -> string -> bool
