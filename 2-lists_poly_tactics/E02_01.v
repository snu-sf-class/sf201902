Require Import P02.


Check count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.


