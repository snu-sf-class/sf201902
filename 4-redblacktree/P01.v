Require Export D.



(** **** Exercise: 2 stars (ins_SearchTree)  *)
(** This one is pretty easy, even without proof automation.
  Copy-paste your proof of insert_SearchTree from Extract.v.
  You will need to apply [balance_SearchTree] in two places.
 *)
 Lemma ins_SearchTree:
 forall x vx s lo hi,
                  lo <= int2Z x ->
                  int2Z x < hi ->
                  SearchTree' lo s hi ->
                  SearchTree' lo (ins x vx s) hi.
Proof. exact FILL_IN_HERE. Qed.

