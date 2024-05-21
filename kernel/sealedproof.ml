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
open Cooking

type 'a delayed_universes =
| PrivateMonomorphic of 'a
| PrivatePolymorphic of Univ.ContextSet.t

type sealed_proofterm = Constr.t * unit delayed_universes

type sealed =
| Indirect of substitution list * cooking_info list * DirPath.t * int (* subst, discharge, lib, index *)

type sealedtab = {
  sealed_len : int;
  (** Size of the above map *)
  sealed_dir : DirPath.t;
}
let empty_sealedtab = {
  sealed_len = 0;
  sealed_dir = DirPath.dummy;
}

let repr (Indirect (s, ci, dp, i)) = (s, ci, dp, i)

let create dp tab =
  let id = tab.sealed_len in
  let sealed_dir =
    if DirPath.equal dp tab.sealed_dir then tab.sealed_dir
    else if DirPath.equal tab.sealed_dir DirPath.dummy then dp
    else CErrors.anomaly
      (Pp.str "Using the same sealed table for multiple dirpaths.") in
  let ntab = { sealed_dir; sealed_len = id + 1 } in
  Indirect ([], [], dp, id), ntab

let subst_sealed sub = function
| Indirect (s, ci, dp, i) -> Indirect (sub :: s, ci, dp, i)

let discharge_sealed info = function
| Indirect (s, ci, dp, i) ->
  assert (CList.is_empty s);
  Indirect ([], info :: ci, dp, i)

module HandleMap = Int.Map

type sealed_handle = int

let repr_handle i = i

let mem_handle i { sealed_len = n; _ } = i < n
