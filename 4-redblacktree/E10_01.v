Require Import P10.



Check insert_is_redblack:
  forall x xv s n, is_redblack s Red n ->
                    exists n', is_redblack (insert x xv s) Red n'.
