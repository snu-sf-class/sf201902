Require Import P01.



Check split_len: forall (l : list nat) (k : nat) (l1 l2 : list nat),
  k <= length l ->
  split k l = (l1, l2) ->
  length l1 = k /\ length l = length l1 + length l2.

