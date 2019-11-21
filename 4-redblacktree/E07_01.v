Require Import P07.



Check is_redblack_toblack:
  forall s n, is_redblack s Red n -> is_redblack s Black n.


