Require Import P01.


Check ins_SearchTree:  forall x vx s lo hi,
lo <= int2Z x ->
int2Z x < hi ->
SearchTree' lo s hi ->
SearchTree' lo (ins x vx s) hi.


