(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Cooking
open Constr

val cook_sealed_proofterm : cooking_info list ->
  Sealedproof.sealed_proofterm -> Sealedproof.sealed_proofterm

val cook_constant :
  Environ.env -> cooking_info -> constant_body -> (Sealedproof.sealed, unit) pconstant_body

val cook_inductive :
  cooking_info -> mutual_inductive_body -> mutual_inductive_body

val cook_rel_context : cooking_info -> rel_context -> rel_context
