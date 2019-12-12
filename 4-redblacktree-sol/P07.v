
Require Export P06.



Hint Constructors is_redblack.
Lemma is_redblack_toblack:
  forall s n, is_redblack s Red n -> is_redblack s Black n.
Proof.
  intros.
  inv H; eauto.
Qed.
