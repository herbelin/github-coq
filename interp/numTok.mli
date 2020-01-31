(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Numerals in different forms: signed or unsigned, possibly with
    fractional part and exponent *)

type sign = SPlus | SMinus

module UnsignedNat :
sig
  type t
  val of_string : string -> t
  val to_string : t -> string
  val compare : t -> t -> int
end

module SignedNat :
sig
  type t = sign * UnsignedNat.t
  val of_string : string -> t
  val to_string : t -> string
  val to_bigint : t -> Bigint.bigint
end

(** {6 Unsigned numerals for the lexer } *)

module Unsigned :
sig
  type t
  val equal : t -> t -> bool
  val is_nat : t -> bool
  val to_nat : ?loc:Loc.t -> t -> string
    (** [to_nat s]
        Raise an error if not a natural number *)

  val to_string : t -> string
  val of_string : string -> t option
  val parse : char Stream.t -> t
    (** Parse a positive numeral.
        Precondition: the first char on the stream is a digit (\[0-9\]).
        Precondition: at least two extra chars after the numeral to parse.
        The numeral can contains _, e.g. to separate thousands *)
end

(** {6 Signed numerals for the notations } *)

module Signed :
sig
  type t = sign * Unsigned.t
  val equal : t -> t -> bool
  val is_zero : t -> bool
  val of_nat : UnsignedNat.t -> t
  val of_int : SignedNat.t -> t
  val of_int_string : string -> t
  val to_int : t -> SignedNat.t option
  val to_string : t -> string
  val of_string : string -> t option
  val to_bigint : t -> Bigint.bigint option
  val of_bigint : Bigint.bigint -> t

  val of_decimal_and_exponent : SignedNat.t -> UnsignedNat.t option -> SignedNat.t option -> t
  val to_decimal_and_exponent : t -> SignedNat.t * UnsignedNat.t option * SignedNat.t option
    (* takes n,p,q such that the number is n.p*2^q *)

  val to_bigint_fraction : t -> Bigint.bigint * Bigint.bigint
  val of_bigint_fraction : Bigint.bigint -> Bigint.bigint -> t
    (* takes n and p such that the number is n/2^p *)

  val is_int_less_than : t -> UnsignedNat.t -> bool 
    (** Test if an integer whose absolute value is bounded *)
end
