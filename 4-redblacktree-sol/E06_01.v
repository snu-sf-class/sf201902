Require Import P06.



Check ins_relate:
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (ins k v t) (t_update cts (int2Z k) v).


