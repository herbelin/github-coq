(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Flags
open Unification

(* Configuration for rewriting tactics *)

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

(* Flags for bare rewrite < 8.8 *)

let rewrite_core_unif_flags = {
  modulo_conv_on_closed_terms = None;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = empty_transparent_state;
  modulo_delta_types = empty_transparent_state;
  check_applied_meta_types = true;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  frozen_evars = Evar.Set.empty;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = true;
}

let rewrite_unif_flags = {
  core_unify_flags = rewrite_core_unif_flags;
  merge_unify_flags = rewrite_core_unif_flags;
  subterm_unify_flags = rewrite_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
    (* allow_K does not matter in practice because calls w_typed_unify *)
  resolve_evars = true
}

let rewrite_conv_closed_core_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
    (* We have this flag for historical reasons, it has e.g. the consequence *)
    (* to rewrite "?x+2" in "y+(1+1)=0" or to rewrite "?x+?x" in "2+(1+1)=0" *)

  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
    (* Combined with modulo_conv_on_closed_terms, this flag allows since 8.2 *)
    (* to rewrite e.g. "?x+(2+?x)" in "1+(1+2)=0" *)

  modulo_delta = empty_transparent_state;
  modulo_delta_types = full_transparent_state;
  check_applied_meta_types = true;
  use_pattern_unification = true;
    (* To rewrite "?n x y" in "y+x=0" when ?n is *)
    (* a preexisting evar of the goal*)

  use_meta_bound_pattern_unification = true;

  frozen_evars = Evar.Set.empty;
    (* This is set dynamically *)

  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = true;
}

let rewrite_conv_closed_unif_flags = {
  core_unify_flags = rewrite_conv_closed_core_unif_flags;
  merge_unify_flags = rewrite_conv_closed_core_unif_flags;
  subterm_unify_flags = rewrite_conv_closed_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

let rewrite_keyed_core_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
    (* We have this flag for historical reasons, it has e.g. the consequence *)
    (* to rewrite "?x+2" in "y+(1+1)=0" or to rewrite "?x+?x" in "2+(1+1)=0" *)

  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
    (* Combined with modulo_conv_on_closed_terms, this flag allows since 8.2 *)
    (* to rewrite e.g. "?x+(2+?x)" in "1+(1+2)=0" *)

  modulo_delta = full_transparent_state;
  modulo_delta_types = full_transparent_state;
  check_applied_meta_types = true;
  use_pattern_unification = true;
    (* To rewrite "?n x y" in "y+x=0" when ?n is *)
    (* a preexisting evar of the goal*)

  use_meta_bound_pattern_unification = true;

  frozen_evars = Evar.Set.empty;
    (* This is set dynamically *)

  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = true;

  modulo_eta = true;
}

let rewrite_keyed_unif_flags = {
  core_unify_flags = rewrite_keyed_core_unif_flags;
  merge_unify_flags = rewrite_keyed_core_unif_flags;
  subterm_unify_flags = rewrite_keyed_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

(* Flags readers *)

let rewrite_hyp_side_condition_fix = function
  | None -> Flags.version_strictly_greater Flags.V8_7
  | Some flags -> flags.rewrite_hyp_side_condition_fix

let rewrite_unify_flags = function
  | None -> if is_keyed_unification () then rewrite_keyed_unif_flags else rewrite_conv_closed_unif_flags;
  | Some flags -> flags.unify_flags

let rewrite_instantiate_unify_flags = function
  | None -> if Flags.version_strictly_greater Flags.V8_7
            then rewrite_keyed_unif_flags else rewrite_unif_flags
  | Some flags -> flags.instantiate_unify_flags

let rewrite_keyed_unification = function
  | None -> Flags.version_strictly_greater Flags.V8_7 && Unification.is_keyed_unification ()
  | Some flags -> flags.keyed_unification

(* A version of the rewrite configuration which corresponds to what
   rewrite was doing by default wrt unification in 8.7, and with both
   dep_proof and freeze_evars true (up to the hyp_side_condition_fix) *)

let simple_rewrite_unif_flags = {
  instantiate_unify_flags = rewrite_unif_flags;
  unify_flags = rewrite_conv_closed_unif_flags;
  keyed_unification = false;
  }

let simple_rewrite_flags = {
  rewrite_unif_flags = Some simple_rewrite_unif_flags;
  rewrite_dep_proof_ok = true;
  rewrite_freeze_evars = true;
  rewrite_hyp_side_condition_fix = true;
  }

(* frzevars and dep_proof were already determined statically *)

let make_static_rewrite_unif_flags = function
  | VOld | V8_5 | V8_6 | V8_7 -> None (* Dynamic behavior *)
  | Current -> Some {
      instantiate_unify_flags = rewrite_instantiate_unify_flags None;
      unify_flags = rewrite_conv_closed_unif_flags;
      keyed_unification = rewrite_keyed_unification None;
    }

let make_rewrite_flags ?(frzevars=false) ?(dep_proof_ok=true) version = {
  rewrite_unif_flags = make_static_rewrite_unif_flags version;
  rewrite_dep_proof_ok = dep_proof_ok;
  rewrite_freeze_evars = frzevars;
  rewrite_hyp_side_condition_fix = rewrite_hyp_side_condition_fix None;
}
