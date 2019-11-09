(* A shorter proof of maybe_swap_idempotent which is at Perm.v, Volume 3 *)

Theorem maybe_swap_idempotent:
  forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros. do 2 (destruct al; eauto).

  simpl; bdestruct (n0 <? n); simpl;
    [ bdestruct (n <? n0) | bdestruct (n0 <? n) ];
    eauto; nia.
  
  (* repeat (simpl; match goal with [|- context[?a <? ?b]] => bdestruct(a <? b) end)
     ; eauto; nia. *)
Qed.
