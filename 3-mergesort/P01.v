Require Export D.



Lemma split_len l k l1 l2
      (LEN: k <= length l)
      (SPLIT: split k l = (l1,l2)):
  length l1 = k /\ length l = length l1 + length l2.
Proof. exact FILL_IN_HERE. Qed.

