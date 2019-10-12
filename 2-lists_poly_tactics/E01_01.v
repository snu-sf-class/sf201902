Require Import P01.


Check rev_app_distr: forall (X: Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.


