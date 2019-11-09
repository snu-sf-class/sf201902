Require Import P04.



Check merge_len: forall (fuel:nat) (l1 l2 : list nat)
    (FUEL: fuel >= length l1 + length l2),
    length (merge' fuel l1 l2) = length l1 + length l2.

