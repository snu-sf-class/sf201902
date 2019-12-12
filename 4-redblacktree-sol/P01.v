
Require Export D.
Require Export Lia.


(** **** Exercise: 2 stars (ins_SearchTree)  *)
(** This one is pretty easy, even without proof automation.
  Copy-paste your proof of insert_SearchTree from Extract.v.
  You will need to apply [balance_SearchTree] in two places.
 *)

(* Define hexploit tactic that was also used at merge_sort assignment *)
Lemma __mp__: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.
Ltac hexploit H := eapply __mp__; [eapply H|].

Ltac gendep x := generalize dependent x.

Lemma ins_SearchTree:
forall x vx s lo hi,
                  lo <= int2Z x ->
                  int2Z x < hi ->
                  SearchTree' lo s hi ->
                  SearchTree' lo (ins x vx s) hi.
Proof.
  intros x vx s.
  induction s.
  { intros. simpl. constructor; constructor; nia. }
  { intros. simpl. inversion H1. subst.
    bdestruct (ltb x k).
    { apply balance_SearchTree; try assumption.
      eapply IHs1; try assumption; try nia. }
    { bdestruct (ltb k x).
      { apply balance_SearchTree; try assumption.
        eapply IHs2; try assumption; try nia. }
      { assert (HEQ: int2Z x = int2Z k). nia.
        constructor; rewrite HEQ in *; assumption.  }
    }
  }
Qed.

