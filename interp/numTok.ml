(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** We keep the string to preserve the user representation,
    e.g. "e"/"E" or the presence of leading 0s, or the presence of a +
    in the exponent *)

module UnsignedNat =
struct
  type t = string
  let of_string s =
    assert (String.length s > 0);
    assert (s.[0] <> '-');
    String.(concat "" (split_on_char '_' s))
  let to_string s = s

  (** Comparing two raw numbers (base 10, big-endian, non-negative).
      A bit nasty, but not critical: only used to decide when a
      number is considered as large (see warnings above). *)

  exception Comp of int

  let rec compare s s' =
    let l = String.length s and l' = String.length s' in
    if l < l' then - compare s' s
    else
      let d = l-l' in
      try
        for i = 0 to d-1 do if s.[i] != '0' then raise (Comp 1) done;
        for i = d to l-1 do
          let c = Util.pervasives_compare s.[i] s'.[i-d] in
          if c != 0 then raise (Comp c)
        done;
        0
      with Comp c -> c
end

type sign = SPlus | SMinus

module SignedNat =
struct
  type t = sign * UnsignedNat.t
  let of_string n =
    let sign,n =
      if String.length n > 0 && n.[0] = '-'
      then (SMinus,String.sub n 1 (String.length n - 1))
      else (SPlus,n) in
    (sign,UnsignedNat.of_string n)
  let to_string (s,n) =
    (match s with SPlus -> "" | SMinus -> "-") ^ UnsignedNat.to_string n
  let to_bigint s = Bigint.of_string (to_string s)
  let of_bigint n =
    let sign, n = if Bigint.is_strictly_neg n then (SMinus, Bigint.neg n) else (SPlus, n) in
    (sign, Bigint.to_string n)
end

module Unsigned =
struct

  type t = {
    int : string;  (** -?\[0-9\]\[0-9_\]* *)
    frac : string;  (** empty or \[0-9_\]+ *)
    exp : string  (** empty or \[eE\]\[+-\]?\[0-9\]\[0-9_\]* *)
  }

  let equal n1 n2 =
    String.(equal n1.int n2.int && equal n1.frac n2.frac && equal n1.exp n2.exp)

  let parse =
    let buff = ref (Bytes.create 80) in
    let store len x =
      let open Bytes in
      if len >= length !buff then
        buff := cat !buff (create (length !buff));
      set !buff len x;
      succ len in
    let get_buff len = Bytes.sub_string !buff 0 len in
    (* reads [0-9_]* *)
    let rec number len s = match Stream.peek s with
      | Some (('0'..'9' | '_') as c) -> Stream.junk s; number (store len c) s
      | _ -> len in
    fun s ->
    let i = get_buff (number 0 s) in
    let f =
      match Stream.npeek 2 s with
      | '.' :: (('0'..'9' | '_') as c) :: _ ->
         Stream.junk s; Stream.junk s; get_buff (number (store 0 c) s)
      | _ -> "" in
    let e =
      match (Stream.npeek 2 s) with
      | (('e'|'E') as e) :: ('0'..'9' as c) :: _ ->
         Stream.junk s; Stream.junk s; get_buff (number (store (store 0 e) c) s)
      | (('e'|'E') as e) :: (('+'|'-') as sign) :: _ ->
         begin match Stream.npeek 3 s with
         | _ :: _ :: ('0'..'9' as c) :: _ ->
            Stream.junk s; Stream.junk s; Stream.junk s;
            get_buff (number (store (store (store 0 e) sign) c) s)
         | _ -> ""
         end
      | _ -> "" in
    { int = i; frac = f; exp = e }

  let to_string n =
    n.int ^ (if n.frac = "" then "" else "." ^ n.frac) ^ n.exp

  let of_string s =
    if s = "" || s.[0] < '0' || s.[0] > '9' then None else
      let strm = Stream.of_string (s ^ "  ") in
      let n = parse strm in
      if Stream.count strm >= String.length s then Some n else None

  let to_nat ?loc = function
    | { int = i; frac = ""; exp = "" } -> i
    | _ -> CErrors.user_err ?loc (Pp.str "This number is not a natural number.")

  let is_nat = function
    | { int = _; frac = ""; exp = "" } -> true
    | _ -> false

end

open Unsigned

module Signed =
struct

  type t = sign * Unsigned.t

  let equal (s1,n1) (s2,n2) =
    s1 = s2 && equal n1 n2

  let is_zero s =
    let rec aux i =
      Int.equal (String.length s) i || (s.[i] == '0' && aux (i+1))
    in aux 0
  let is_zero = function
    | (SPlus,{int;frac;exp}) -> is_zero int && is_zero frac
    | _ -> false

  let of_decimal_and_exponent (sign,int) f e =
    let exp = match e with Some e -> "e" ^ SignedNat.to_string e | None -> "" in
    let frac = match f with Some f -> UnsignedNat.to_string f | None -> "" in
    sign, { int; frac; exp }

  let to_decimal_and_exponent (sign, { int; frac; exp }) =
    let e =
      if exp = "" then None else
        Some (match exp.[1] with
        | '-' -> SMinus, String.sub exp 2 (String.length exp - 2)
        | '+' -> SPlus, String.sub exp 2 (String.length exp - 2)
        | _ -> SPlus, String.sub exp 1 (String.length exp - 1)) in
    let f = if frac = "" then None else Some frac in
    (sign, int), f, e

  let of_int_and_exponent i e =
    of_decimal_and_exponent i None e

  let of_nat i =
    (SPlus,{ int = i; frac = ""; exp = "" })

  let of_int (s,i) =
    (s,{ int = i; frac = ""; exp = "" })

  let of_int_string s = of_int (SignedNat.of_string s)

  let to_string (sign,u) =
    (match sign with SPlus -> "" | SMinus -> "-") ^ Unsigned.to_string u

  let to_int = function
    | (s, { int = i; frac = ""; exp = "" }) -> Some (s,i)
    | _ -> None

  let of_string s =
    if s = "" || s.[0] <> '-' && (s.[0] < '0' || s.[0] > '9') then None else
      let strm = Stream.of_string (s ^ "  ") in
      let sign = if s.[0] = '-' then (Stream.junk strm; SMinus) else SPlus in
      let n = parse strm in
      if Stream.count strm >= String.length s then Some (sign,n) else None

  let to_bigint = function
    | (sign, { int = n; frac = ""; exp = "" }) ->
      let n = String.(concat "" (split_on_char '_' n)) in
      Some (SignedNat.to_bigint (sign,n))
    | _ -> None

  let of_bigint n =
    let sign, int = SignedNat.of_bigint n in
    (sign, { int; frac = ""; exp = "" })

  let to_bigint_fraction (s, { int; frac; exp }) =
    let s = match s with SPlus -> "" | SMinus -> "-" in
    let i = Bigint.of_string (s ^ int ^ frac) in
    let e =
      let e = if exp = "" then Bigint.zero else match exp.[1] with
      | '+' -> Bigint.of_string (String.sub exp 2 (String.length exp - 2))
      | '-' -> Bigint.(neg (of_string (String.sub exp 2 (String.length exp - 2))))
      | _ -> Bigint.of_string (String.sub exp 1 (String.length exp - 1)) in
      Bigint.(sub e (of_int (String.length frac))) in
    (i,e)

  let of_bigint_fraction i e =
    of_int_and_exponent (SignedNat.of_bigint i) (Some (SignedNat.of_bigint e))

  let is_int_less_than (s, { int; frac; exp }) i =
    frac = "" && exp = "" && compare int i >= 0

end
