Require Export P01.



Lemma empty_tree_SearchTree: SearchTree empty_tree.
Proof.
  unfold empty_tree. apply ST_intro with (lo := 0) (hi := 1). constructor. nia.
Qed.
