Require Export P01.



(** **** Exercise: 2 stars, standard (andb_true_elim2)  

    Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  exact FILL_IN_HERE.
Qed.

