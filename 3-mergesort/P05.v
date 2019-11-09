Require Export P04.



Lemma merge_sorted fuel l1 l2
      (FUEL: fuel >= length l1 + length l2)
      (SORTED1: sorted l1) (SORTED2: sorted l2):
  sorted (merge' fuel l1 l2).
Proof. exact FILL_IN_HERE. Qed.

