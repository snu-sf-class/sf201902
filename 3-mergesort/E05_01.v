Require Import P05.



Check merge_sorted: forall (fuel:nat) (l1 l2 : list nat)
    (FUEL: fuel >= length l1 + length l2)
    (SORTED1: sorted l1) (SORTED2: sorted l2),
    sorted (merge' fuel l1 l2).

