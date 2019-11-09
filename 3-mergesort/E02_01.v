Require Import P02.



Check split_permutation: forall (l : list nat) (k : nat) (l1 l2 : list nat),
    split k l = (l1, l2) -> Permutation l (l1 ++ l2).

