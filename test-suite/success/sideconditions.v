Set Tactic Side Conditions Mode "First".

Record T A B := {fst : A -> B; snd : B -> A}.

Goal (0 = 0 -> 1 = 1 -> True -> False) -> True -> False.
intros.
apply H in H0.

Goal (0=0 -> T True False) -> True -> False.
intros.
apply H in H0.

Goal (0=0 -> True <-> False) -> True -> False.
intros.
apply H in H0.

Goal (0=0 -> 1=2) -> 1=2.
intros.
rewrite H.

Goal (0=0 -> 1=2) -> 1=2 -> True.
intros.
rewrite H in H0.

Goal (0=0 -> True /\ True) -> True.
intros [].

Goal (0=0 -> True /\ True) -> True.
intros.
induction H.

Goal (0=0 -> True /\ True) -> True.
intros.
destruct H.
