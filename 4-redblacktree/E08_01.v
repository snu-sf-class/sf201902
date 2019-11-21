Require Import P08.



Check makeblack_fiddle:
  forall s n, is_redblack s Black n ->
            exists n, is_redblack (makeBlack s) Red n.


