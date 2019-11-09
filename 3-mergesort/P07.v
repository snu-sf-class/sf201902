Require Export P06.



Lemma merge_sort_sorted fuel l
      (FUEL: fuel >= length l):
  sorted (merge_sort' fuel l).
Proof. exact FILL_IN_HERE. Qed.

Theorem merge_sort_correct: is_a_sorting_algorithm merge_sort.
Proof.
  split.
  - apply merge_sort_permutation; eauto.
  - apply merge_sort_sorted; eauto.
Qed.

