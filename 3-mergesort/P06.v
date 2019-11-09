Require Export P05.



Lemma merge_sort_permutation fuel l
      (FUEL: fuel >= length l):
  Permutation l (merge_sort' fuel l).
Proof. exact FILL_IN_HERE. Qed.

