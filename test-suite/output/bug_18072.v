(* Check that dependent goal names are kept *)

Goal let n:=0 in exists x, x = 0.
intro.
unshelve esplit.
simpl.
Show.
simpl in n.
Show.
clearbody n.
Show.
change (id nat).
Show.
change (id nat) in n.
Show.
clear n.
Show.
set (n := 0).
Show.
pose (m := 0).
Show.
rename m into p.
Show.
move n after p.
Show.
remember 0 as q.
exact 0.
reflexivity.
Qed.
