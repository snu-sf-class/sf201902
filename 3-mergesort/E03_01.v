Require Import P03.



Check merge_permutation: forall (fuel:nat) (l1 l2 : list nat)
    (FUEL: fuel >= length l1 + length l2),
    Permutation (l1++l2) (merge' fuel l1 l2).

