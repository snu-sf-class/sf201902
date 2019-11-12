(** * Final Correctness Theorem *)

Fixpoint map_reduce {A C} (f: A -> C -> C) (c0: C) (l: list A) : C :=
  match l with
  | nil => c0
  | hd::tl => f hd (map_reduce f c0 tl)
  end.

Theorem search_tree_correct: forall (l: list (key*V)) k,
  lookup k (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree        l) = 
           (map_reduce (fun kv tm => t_update tm (fst kv) (snd kv)) (t_empty default) l) k.
Proof.
  assert (ABS: forall l,
     Abs (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree        l)
         (map_reduce (fun kv tm => t_update tm (fst kv) (snd kv)) (t_empty default) l)).
  { intros. induction l; simpl; eauto using insert_relate. }
  intros. eauto using lookup_relate.
Qed.
