Require Export Perm Sort.
Require Export Lia.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(* [hexploit]: A very useful tactic, developed by Gil Hur.

   Suppose we have:

     H: P1 -> ... -> Pn -> Q
     ========================
     G

   [hexploit H] turns this goal into the following (n+1) subgoals:

     H: P1 -> ... -> Pn -> Q
     =========================
     P1

     ...

     H: P1 -> ... -> Pn -> Q
     =========================
     Pn

     H: P1 -> ... -> Pn -> Q
     =========================
     Q -> G
*)

Lemma __mp__: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Ltac hexploit H := eapply __mp__; [eapply H|].

Example hexploit_example: forall (P Q: Prop) n
    (ASM: P /\ Q)
    (IMP: P -> Q -> n >= 5),
  n > 2.
Proof.
  intros.
  hexploit IMP.
  { destruct ASM; eauto. }
  { destruct ASM; eauto. }
  intros. nia.
Qed.

(***
    Definitions
 ***)

Fixpoint split (k: nat) (l: list nat) : list nat * list nat :=
  match k with
  | 0 => (nil, l)
  | S k' =>
    match l with
    | nil => (nil, l)
    | a::l' =>
      match split k' l' with
      | (l1,l2) => (a::l1, l2)
      end
    end
  end.

Compute split 3 [1;2;3;4;5].

Fixpoint merge' (fuel: nat) (l1 l2: list nat) : list nat :=
  match fuel with
  | 0 => nil
  | S fuel' =>
    match l1,l2 with
    | [],_ => l2
    | _,[] => l1
    | a::l1',b::l2' =>
      if a <=? b
      then a::merge' fuel' l1' l2
      else b::merge' fuel' l1 l2'
    end
  end.

Definition merge l1 l2 := merge' (length l1 + length l2) l1 l2.

Compute merge [1; 4] [3; 5].
Compute merge [2] [].

Fixpoint merge_sort' (fuel: nat) (l: list nat) : list nat :=
  match fuel with
  | 0 => l
  | S fuel' =>
    match l with
    | [] | [_] => l
    | _ =>
      match split (Nat.div2 (length l)) l with
      | (l1,l2) => merge (merge_sort' fuel' l1) (merge_sort' fuel' l2)
      end
    end
  end.

Definition merge_sort l := merge_sort' (length l) l.

Compute merge_sort [10;3;7;2;3;5;8].
Compute merge_sort [2;1].

Hint Constructors Permutation sorted.

(***
    Proofs
 ***)

 
