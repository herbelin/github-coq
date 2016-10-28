(* Various scopes issues *)

(* Appel's example (working from 8.5) *)

Bind Scope s with bool.
Definition force (x: bool) := x.
Notation "0" := true : s.
Definition x : bool := 0.
Definition y := force 0.

(* Jason's example *)

Unset Immediate Only Implicit Scope.

Inductive nat1 := O1 | S1 (_ : nat1).
Inductive nat2 := O2 | S2 (_ : nat2).
Axiom add1 : nat1 -> nat1 -> nat1.
Axiom add2 : nat2 -> nat2 -> nat2.
Axiom conv12 : nat1 -> nat2.
Axiom conv21 : nat2 -> nat1.
Delimit Scope nat1_scope with nat1.
Delimit Scope nat2_scope with nat2.
Bind Scope nat1_scope with nat1.
Bind Scope nat2_scope with nat2.
Notation "1" := (S1 O1) : nat1_scope.
Notation "1" := (S2 O2) : nat2_scope.
Notation "++++++" := (O1) : nat1_scope.
Notation "a + b" := (add1 a b) : nat1_scope.
Notation "a + b" := (add2 a b) : nat2_scope.
Notation "a +F b" := (add1 a%nat1 b%nat1) (at level 50, left associativity) : nat1_scope.
Notation "a +F b" := (add2 a%nat1 b%nat1) (at level 50, left associativity) : nat2_scope.

(** verify that bind scope worked *)
Check conv12 (1 : nat1).
Fail Check conv12 (1 : nat2).
Check conv21 (1 : nat2).
Fail Check conv21 (1 : nat1).
(* all correct *)

(** I expect that a bound argument scope will bring that scope to the
    top for that argument; if [foo] has one argument with scope
    [bar_scope] (delimited by [bar]), [foo x] should be equivalent to
    [foo (x)%bar]. *)

(** verify that bound scopes take precedence over explicit scopes above them *)
Check (conv12 1)%nat2.
Check (conv12 1 +F conv12 1)%nat2.
Check (conv12 1)%nat1.
Check (conv12 (conv21 (conv12 1) +F conv21 (conv12 1)))%nat2.
Check (conv12 (conv21 (conv12 1) +F conv21 (conv12 1)))%nat1.
(** so far so good *)
Check (conv12 ((fun _ => 1) tt)%nat1). (* good *)
Check (conv12 ((fun _ => 1) tt)). (* bad!  [1] should be interpreted in [nat1_scope] automatically *)
Check (conv12 ((fun _ => 1) tt +F (fun _ => 1) tt)). (* but if we use a notation that forces the scopes, things work... *)
Check (conv12 ((fun _ => 1) tt + (fun _ => 1) tt)). (* ... but not if the notation assumes its scopes automatically *)
Check (conv12 (fst (1, tt)))%nat1. (* good *)
Check conv12 (fst (1, tt)). (* bad!  [1] should be interpreted in [nat1_scope] automatically *)
(** Furthermore, implicit scopes should be layered, and certainly should not be overwritten by empty scopes *)
Check (conv12 ++++++). (* good *)
Check (conv12 ++++++%nat1). (* good *)
Check (conv12 (++++++%nat2)%nat1). (* good *)
Check (conv12 (++++++%nat1)%nat2). (* good *)
Check (conv12 (fst (1, ++++++))). (* bad! the [fst (_, _)] should not remove the implicit scopes above it! *)

(* Jacques-Henri's examples *)

Delimit Scope scope with S.
Notation "#" := 0 : scope.
Definition foo (n:nat) := n.
Arguments foo _%S.
Check (foo #).
Definition bar (n:nat -> nat) := n 0.
Arguments bar _%S.
Check (bar (fun _ => #)).
Check (bar (fun _ => #)%S).
