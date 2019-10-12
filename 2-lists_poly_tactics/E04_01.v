Require Import P04.



Check rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.


