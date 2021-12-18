(* Check that a field can be defined under parameters *)
Module Type T. End T.
Module Type S (X : T). Axiom U : Type. End S.
Module Type R (X : T). Declare Module A : S. End R.
Module Type Q := R with Definition A.U := nat.
Module M. End M.
Module F (X : Q M).
  Module B := X.A M.
  Goal B.U = nat.
  reflexivity.
  Qed.
End F.
