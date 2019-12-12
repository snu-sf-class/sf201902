Require Export P07.



Hint Constructors is_redblack.
Hint Resolve is_redblack_toblack.
Lemma makeblack_fiddle:
  forall s n, is_redblack s Black n ->
            exists n, is_redblack (makeBlack s) Red n.
Proof.
  intros.
  induction H.
  { simpl. eauto. }
  { exists (S n). constructor; eauto. }
  { exists (S n). constructor; eauto. }
Qed.

