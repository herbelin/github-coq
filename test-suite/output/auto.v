(* testing info/debug auto/eauto *)

Goal 0=0.
info_auto.
Undo.
debug auto.
Undo.
info_eauto.
Undo.
debug eauto.
Qed.
