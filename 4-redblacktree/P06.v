Require Export P05.



Theorem ins_relate:
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (ins k v t) (t_update cts (int2Z k) v).
Proof. exact FILL_IN_HERE. Qed.

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

