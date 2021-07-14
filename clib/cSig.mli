(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Missing pervasive types from OCaml stdlib *)

type ('a, 'b) union = Inl of 'a | Inr of 'b
(** Union type *)

type 'a until = Stop of 'a | Cont of 'a
(** Used for browsable-until structures. *)

type (_, _) eq = Refl : ('a, 'a) eq

module type SetS =
sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    (* val disjoint: t -> t -> bool from 4.08.0 *)
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    (* val map: (elt -> elt) -> t -> t from 4.04 *)
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    (* val filter_map: (elt -> elt option) -> t -> t from 4.11.0 *)
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    (* val min_elt_opt: t -> elt option from 4.05 *)
    val max_elt: t -> elt
    (* val max_elt_opt: t -> elt option from 4.05 *)
    val choose: t -> elt
    (* val choose_opt: t -> elt option from 4.05 *)
    val split: elt -> t -> t * bool * t
    (* val find: elt -> t -> elt from 4.01 *)
    (* val find_opt: elt -> t -> elt option from 4.05 *)
    (* val find_first: (elt -> bool) -> t -> elt from 4.05 *)
    (* val find_first_opt: (elt -> bool) -> t -> elt option from 4.05 *)
    (* val find_last: (elt -> bool) -> t -> elt from 4.05 *)
    (* val find_last_opt: (elt -> bool) -> t -> elt option from 4.05 *)
    val of_list: elt list -> t
    (* val to_seq_from : elt -> t -> elt Seq.t from 4.07 *)
    (* val to_seq : t -> elt Seq.t from 4.07 *)
    (* val to_rev_seq : t -> elt Seq.t from 4.12 *)
    (* val add_seq : elt Seq.t -> t -> t from 4.07 *)
    (* val of_seq : elt Seq.t -> tend from 4.07 *)
end
(** Redeclaration of OCaml set signature, to preserve compatibility. See OCaml
    documentation for more information. *)

module type MapS =
sig
    type key
    type (+'a) t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val mem: key -> 'a t -> bool
    val add: key -> 'a -> 'a t -> 'a t
    (* when Coq requires OCaml 4.06 or later, can add:

         val update : key -> ('a option -> 'a option) -> 'a t -> 'a t

       allowing Coq to use OCaml's "update"
    *)
    val singleton: key -> 'a -> 'a t
    val remove: key -> 'a t -> 'a t
    val merge:
         (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union:
      (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    val exists: (key -> 'a -> bool) -> 'a t -> bool
    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    (* val filter_map: (key -> 'a -> 'b option) -> 'a t -> 'b t from 4.11 *)
    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal: 'a t -> int
    val bindings: 'a t -> (key * 'a) list
    val min_binding: 'a t -> (key * 'a)
    (* val min_binding_opt: 'a t -> (key * 'a) option from 4.05 *)
    val max_binding: 'a t -> (key * 'a)
    (* val max_binding_opt: 'a t -> (key * 'a) option from 4.05 *)
    val choose: 'a t -> (key * 'a)
    val choose_opt: 'a t -> (key * 'a) option
    val split: key -> 'a t -> 'a t * 'a option * 'a t
    val find: key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    (* val find_first: (key -> bool) -> 'a t -> key * 'a from 4.05 *)
    (* val find_first_opt: (key -> bool) -> 'a t -> (key * 'a) option from 4.05 *)
    (* val find_last: (key -> bool) -> 'a t -> key * 'a from 4.05 *)
    (* val find_last_opt: (key -> bool) -> 'a t -> (key * 'a) option from 4.05 *)
    val map: ('a -> 'b) -> 'a t -> 'b t
    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
    (* val to_seq : 'a t -> (key * 'a) Seq.t from 4.07 *)
    (* val to_rev_seq : 'a t -> (key * 'a) Seq.t from 4.12 *)
    (* val to_seq_from : key -> 'a t -> (key * 'a) Seq.t from 4.07 *)
    (* val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t from 4.07 *)
    (* val of_seq : (key * 'a) Seq.t -> 'a t from 4.07 *)
end
