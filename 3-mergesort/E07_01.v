Require Import P07.



Check merge_sort_sorted: forall (fuel:nat) (l : list nat)
    (FUEL: fuel >= length l),
    sorted (merge_sort' fuel l).
