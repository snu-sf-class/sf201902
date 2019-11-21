Require Export P08.



Lemma ins_is_redblack:
  forall x vx s n,
    (is_redblack s Black n -> nearly_redblack (ins x vx s) n) /\
    (is_redblack s Red n -> is_redblack (ins x vx s) Black n).
Proof.
exact FILL_IN_HERE. Qed.
(*
induction s; intro n; simpl; split; intros; inv H; repeat constructor; auto.
destruct (IHs1 n); clear IHs1.
destruct (IHs2 n); clear IHs2.
specialize (H0 H6).
specialize (H2 H7).
clear H H1.
unfold balance. *)
(** You will need proof automation, in a similar style to
   the proofs of [ins_not_E] and [balance_relate]. *)

