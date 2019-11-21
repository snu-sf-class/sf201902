Require Export P07.



Lemma makeblack_fiddle:
  forall s n, is_redblack s Black n ->
            exists n, is_redblack (makeBlack s) Red n.
Proof. exact FILL_IN_HERE. Qed.

