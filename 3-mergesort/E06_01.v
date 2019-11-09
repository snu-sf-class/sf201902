Require Import P06.



Check merge_sort_permutation: forall (fuel:nat) (l: list nat)
    (FUEL: fuel >= length l),
    Permutation l (merge_sort' fuel l).

