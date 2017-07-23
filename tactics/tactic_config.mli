(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Unification

type dep_proof_flag = bool (* true = support rewriting dependent proofs *)
type freeze_evars_flag = bool (* true = don't instantiate existing evars *)

type rewrite_unif_flags = {
  instantiate_unify_flags : unify_flags; (* To search for an instantiated subterm *)
  unify_flags : unify_flags; (* To select the occurrences of a subterm  *)
  keyed_unification : bool;
  }

type rewrite_flags = {
  rewrite_unif_flags : rewrite_unif_flags option; (* None = dynamic *)
  rewrite_dep_proof_ok : dep_proof_flag;
  rewrite_freeze_evars : freeze_evars_flag;
  rewrite_hyp_side_condition_fix : bool; (* true = implement pre-8.8 side condition bug *)
  }

val rewrite_instantiate_unify_flags : rewrite_unif_flags option -> unify_flags
val rewrite_unify_flags : rewrite_unif_flags option -> unify_flags

(* A version of the rewrite configuration which corresponds to what
   rewrite was doing by default wrt unification in 8.7, and with both
   dep_proof and freeze_evars true *)

val simple_rewrite_flags : rewrite_flags

(* Produce rewrite flags depending on version and general options (e.g. Keyed Unification) *)

val make_rewrite_flags :
    ?frzevars:freeze_evars_flag -> ?dep_proof_ok:dep_proof_flag -> Flags.compat_version -> rewrite_flags
