(* Check that types are not uselessly unfolded *)

(* Check here that P returns something of type "option L" and not
   "option (list nat)" *)

Definition L := list nat.

Definition P (e:option L) :=
  match e with
  | None => None
  | Some cl => Some cl
  end.

Print P.

(* Check that the heuristic to solve constraints is not artificially
   dependent on the presence of a let-in, and in particular that the
   second [_] below is not inferred to be n, as if obtained by
   first-order unification with [T n] of the conclusion [T _] of the
   type of the first [_]. *)

(* Note: exact numbers of evars are not important... *)

Inductive T (n:nat) := A : T n.
Check fun n (y:=A n:T n) => _ _ : T n.
Check fun n => _ _ : T n.

(* Check refolding of global fixpoints *)

Module PrimProjRefold.

Set Primitive Projections.
Record sigT A P := { projT1 : A; projT2 : P projT1 }.
Notation "{ x : A &T P }" := (sigT A (fun x => P%_type)) (at level 0, x at level 99) : type_scope.
Arguments projT1 {A P} _.
Arguments projT2 {A P} _.

Fixpoint TELE n :=
  match n with
  | 0 => unit
  | S n => { a : nat &T TELE n }
  end.

Check fun n (x : TELE (S n)) => projT2 x.
Check fun n (x : TELE (S n)) (q:nat) => projT2 x. (* Note: q is useful to force retyping *)

End PrimProjRefold.
