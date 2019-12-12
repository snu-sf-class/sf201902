Require Export P03.



Theorem lookup_relate:
  forall k t cts ,   Abs t cts -> lookup k t =  cts (int2Z k).
Proof.
  intros.
  induction H; try eauto.
  simpl. unfold t_update. unfold combine.
  (* There are a bunch of cases that compare between k0 and k.
     In this situation, you can just stack destructs (or bdestruct in this problem)
     and use 'try nia' to eliminate cases that are non-sense. *)
  bdestruct (ltb k k0); bdestruct (int2Z k0 =? int2Z k);
    bdestruct (int2Z k <? int2Z k0); bdestruct (ltb k0 k); try nia; eauto.
Qed.

