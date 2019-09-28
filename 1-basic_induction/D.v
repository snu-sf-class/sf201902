Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

