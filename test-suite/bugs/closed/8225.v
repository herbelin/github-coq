(* Test passing a number by argument in "rewrite n H" *)

Tactic Notation "rewrite_right" integer(n) hyp(H) :=
  rewrite <- n H.

Ltac rewrite_right' n H :=
  rewrite <- n H.

Goal 0=1 -> 1=0.
intro H.
rewrite_right 1 H.
now_show (0=0).
Undo 2.
rewrite_right' integer:(1) H.
now_show (0=0).
auto.
Qed.

