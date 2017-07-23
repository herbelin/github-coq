(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open EConstr
open Misctypes
open Tactypes

type inversion_status = Dep of constr option | NoDep

type inversion_kind =
  | SimpleInversion
  | FullInversion of Tactic_config.rewrite_flags
  | FullInversionClear of Tactic_config.rewrite_flags

val inv_clause :
  inversion_kind -> or_and_intro_pattern option -> Id.t list ->
    quantified_hypothesis -> unit Proofview.tactic

val inv : inversion_kind -> or_and_intro_pattern option ->
  quantified_hypothesis -> unit Proofview.tactic

val dinv : inversion_kind -> constr option ->
  or_and_intro_pattern option -> quantified_hypothesis -> unit Proofview.tactic

val inv_tac : Tactic_config.rewrite_flags -> Id.t -> unit Proofview.tactic
val inv_clear_tac : Tactic_config.rewrite_flags -> Id.t -> unit Proofview.tactic
val dinv_tac : Tactic_config.rewrite_flags -> Id.t -> unit Proofview.tactic
val dinv_clear_tac : Tactic_config.rewrite_flags -> Id.t -> unit Proofview.tactic
