Require Import P04.


Check lookup_relate:  forall k t cts ,   Abs t cts -> lookup k t =  cts (int2Z k).


