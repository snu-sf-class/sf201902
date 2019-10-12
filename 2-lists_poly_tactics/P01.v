Require Export D.

(* Check app_assoc. *)

Theorem rev_app_distr: forall (X: Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. exact FILL_IN_HERE. Qed.

