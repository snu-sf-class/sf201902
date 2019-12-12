Require Import P09.



Check ins_is_redblack:
  forall x vx s n,
    (is_redblack s Black n -> nearly_redblack (ins x vx s) n) /\
    (is_redblack s Red n -> is_redblack (ins x vx s) Black n).


