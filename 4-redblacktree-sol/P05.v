Require Export P04.



(** **** Exercise: 4 stars (balance_relate)  *)
(** You will need proof automation for this one.  Study the methods used
  in [ins_not_E] and [balance_SearchTree], and try them here.
  Add one clause at a time to your [match goal]. *)
Lemma Abs_helper:
  forall m' t m, Abs t m' ->    m' = m ->     Abs t m.
Proof.
   intros. subst. auto.
Qed.

Ltac contents_equivalent_prover :=
 extensionality x; unfold t_update, combine, t_empty;
 repeat match goal with
  | |- context [if ?A then _ else _] => bdestruct A
 end;
 auto;
 omega.

Theorem balance_relate:
  forall c l k vk r m,
    SearchTree (T c l k vk r) ->
    Abs (T c l k vk r) m ->
    Abs (balance c l k vk r) m.
Proof.
intros.
inv H.
unfold balance.
repeat match goal with
       | H: Abs E _ |- _ => inv H
       | H: Abs (T _ _ _ _ _) _ |- _ => inv H
       | H: SearchTree' _ E _ |- _ => inv H
       | H: SearchTree' _ (T _ _ _ _ _) _ |- _ => inv H
       | |- Abs match c with Red => _ | Black => _ end _ => destruct c
       | |- Abs match ?s with E => _ | T _ _ _ _ _ => _ end _ => destruct s
       | |- Abs (T _ _ _ _ _) _ => apply Abs_T
       | |- Abs E _ => apply Abs_E
       | |- _ => assumption
       | |- _ => eapply Abs_helper; [repeat econstructor; eassumption | ]
       | H: SearchTree' ?lo _ ?hi |- _ = _ => apply SearchTree'_le in H
       | |- _ => contents_equivalent_prover
       end.
Qed.

