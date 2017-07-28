Definition foo '(x,y) := x + y.
Print foo.
Check forall '(a,b), a /\ b.

Require Import Utf8.
Print foo.
Check forall '(a,b), a /\ b.

(* Check printing of "let" expressions *)
Check let f '(x, y) (z t : nat) := x + y + z + t in f.
Check let f (b:bool) '(x,y) z := if b then x + y else z in f.

