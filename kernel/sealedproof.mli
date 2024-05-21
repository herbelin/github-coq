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
open Mod_subst

(** This module implements the handling of sealed proof terms.
    Opaque proof terms are special since:
    - they can be lazily computed and substituted
    - they are stored in an optionally loaded segment of .vo files
    An [sealed] proof terms holds an index into an sealed table. *)

type 'a delayed_universes =
| PrivateMonomorphic of 'a
| PrivatePolymorphic of Univ.ContextSet.t (** local constraints *)

type sealedtab
type sealed

val empty_sealedtab : sealedtab

val create : DirPath.t -> sealedtab -> sealed * sealedtab

type sealed_proofterm = Constr.t * unit delayed_universes

type sealed_handle

module HandleMap : CSig.MapS with type key = sealed_handle

(** Opaque terms are indexed by their library
    dirpath and an integer index. The two functions above activate
    this indirect storage, by telling how to retrieve terms.
*)

val subst_sealed : substitution -> sealed -> sealed

val discharge_sealed : Cooking.cooking_info -> sealed -> sealed

val repr_handle : sealed_handle -> int

val mem_handle : sealed_handle -> sealedtab -> bool

val repr : sealed -> substitution list * Cooking.cooking_info list * DirPath.t * sealed_handle
