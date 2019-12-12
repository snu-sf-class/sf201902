Require Export P02.




Lemma SearchTree_neglects_color:
  forall c c' t1 k v t2
    (HST: SearchTree (T c t1 k v t2)),
    SearchTree (T c' t1 k v t2).
Proof.
  intros.
  inv HST. inv H. econstructor. econstructor; eassumption.
Qed.

(* You can use SearchTree'_le, expand_range_SearchTree'. *)
Lemma insert_SearchTree: forall x vx s,
    SearchTree s -> SearchTree (insert x vx s).
Proof.
  intros.
  inv H.
  unfold insert. unfold makeBlack.
  destruct (ins x vx s) eqn: Hins.
  { apply empty_tree_SearchTree. }
  { eapply expand_range_SearchTree'
      with (lo' := Z.min (int2Z x) lo) (hi' := Z.max ((int2Z x)+1) hi) in H0; try nia.
    apply ins_SearchTree with (x := x) (vx := vx) in H0; try nia.
    rewrite Hins in H0. eapply SearchTree_neglects_color. econstructor. eassumption.
  }
Qed.

