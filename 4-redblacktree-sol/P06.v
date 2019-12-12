Require Export P05.



Theorem ins_relate:
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (ins k v t) (t_update cts (int2Z k) v).
Proof.
  intros.
  induction H0.
  { simpl. eapply Abs_helper. repeat econstructor.
    contents_equivalent_prover. }
  { assert(HSPLIT: SearchTree l /\ SearchTree r).
    { inv H. inv H0. split; econstructor; eauto. }
    inv HSPLIT.
    simpl.
    bdestruct (ltb k k0).
    { apply balance_relate.
      { inv H. inv H3.
        eapply expand_range_SearchTree' in H10.
        econstructor. econstructor; try eassumption.
        { eapply P01.ins_SearchTree; try eassumption. instantiate (1 := Z.min lo (int2Z k)). nia. }
        nia. nia. }
      { eapply Abs_helper.
        { econstructor; eauto. }
        { contents_equivalent_prover. }
      }
    }
    { bdestruct (ltb k0 k).
      { apply balance_relate.
        { inv H. inv H4.
          eapply expand_range_SearchTree' in H12.
          econstructor. econstructor; try eassumption.
          { eapply P01.ins_SearchTree; try eassumption. nia. instantiate (1 := Z.max hi (1 + int2Z k)). nia. }
          nia. nia. }
        { eapply Abs_helper.
          { econstructor; eauto. }
          { contents_equivalent_prover. }
        }
      }
      { replace (int2Z k0) with (int2Z k) by nia.
        rewrite t_update_shadow. constructor; eassumption. }
    }
  }
Qed.

Theorem insert_relate:
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (insert k v t) (t_update cts (int2Z k) v).
Proof.
intros.
unfold insert.
apply makeBlack_relate.
apply ins_relate; auto.
Qed.

(** * Final Correctness Theorem *)

Theorem redblack_correct: forall (l: list (key*D.V)) k,
  lookup k (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree l) =
           (map_reduce (fun kv tm => t_update tm (int2Z (fst kv)) (snd kv)) (t_empty D.default) l) (int2Z k).
Proof.
  assert (ABS: forall l,
     SearchTree (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree l) /\
     Abs (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree l)
         (map_reduce (fun kv tm => t_update tm (int2Z (fst kv)) (snd kv)) (t_empty D.default) l)).
  { intros. induction l; simpl.
    - eauto using empty_tree_SearchTree, empty_tree_relate.
    - destruct IHl.
      eauto using insert_SearchTree, insert_relate.
  }
  intros. eapply lookup_relate, ABS.
Qed.

