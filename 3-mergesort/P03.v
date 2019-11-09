Require Export P02.



Lemma merge_permutation fuel l1 l2
      (FUEL: fuel >= length l1 + length l2):
  Permutation (l1++l2) (merge' fuel l1 l2).
Proof. exact FILL_IN_HERE. Qed.

