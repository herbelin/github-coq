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

type t = {
  tr_var : Var.Pred.t;
  tr_cst : Cpred.t;
}

let empty = {
  tr_var = Var.Pred.empty;
  tr_cst = Cpred.empty;
}

let full = {
  tr_var = Var.Pred.full;
  tr_cst = Cpred.full;
}

let var_full = {
  tr_var = Var.Pred.full;
  tr_cst = Cpred.empty;
}

let cst_full = {
  tr_var = Var.Pred.empty;
  tr_cst = Cpred.full;
}

let is_empty ts =
  Var.Pred.is_empty ts.tr_var && Cpred.is_empty ts.tr_cst

let is_transparent_variable ts id =
  Var.Pred.mem id ts.tr_var

let is_transparent_constant ts cst =
  Cpred.mem cst ts.tr_cst
