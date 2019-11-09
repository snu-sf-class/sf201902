Require Export P03.



Lemma merge_len fuel l1 l2
      (FUEL: fuel >= length l1 + length l2):
  length (merge' fuel l1 l2) = length l1 + length l2.
Proof. exact FILL_IN_HERE. Qed.

