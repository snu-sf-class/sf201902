Require Import P01.



Example test_less_than1: (less_than 2 2) = false.
Proof. reflexivity. Qed.
Example test_less_than2: (less_than 0 2) = true.
Proof. reflexivity. Qed.
Example test_less_than3: (less_than 0 0) = false.
Proof. reflexivity. Qed.
Example test_less_than4: (less_than 3 4) = true.
Proof. reflexivity. Qed.
Example test_less_than5: (less_than 6 15) = true.
Proof. reflexivity. Qed.
Example test_less_than6: (less_than 4 2) = false.
Proof. reflexivity. Qed.

