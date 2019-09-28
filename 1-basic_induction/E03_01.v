Require Import P03.



Check identity_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.

