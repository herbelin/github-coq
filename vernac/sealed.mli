(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a const_entry_body = 'a Entries.proof_output Future.computation

val declare_defined_sealed : ?feedback_id:Stateid.t ->
  Sealedproof.sealed_handle -> Safe_typing.private_constants const_entry_body -> unit
val declare_private_sealed : Safe_typing.exported_sealed -> unit

type sealed_disk

val get_sealed_disk : Sealedproof.sealed_handle -> sealed_disk -> Sealedproof.sealed_proofterm option
val set_sealed_disk : Sealedproof.sealed_handle -> Sealedproof.sealed_proofterm -> sealed_disk -> unit

val get_current_sealed : Sealedproof.sealed_handle -> Sealedproof.sealed_proofterm option
val get_current_constraints : Sealedproof.sealed_handle -> Univ.ContextSet.t option

val dump : ?except:Future.UUIDSet.t -> unit -> sealed_disk * Sealedproof.sealed_handle Future.UUIDMap.t

module Summary :
sig
  type t
  val init : unit -> unit
  val freeze : unit -> t
  val unfreeze : t -> unit
  val join : ?except:Future.UUIDSet.t -> unit -> unit
end
