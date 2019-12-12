Require Export P08.


(* is_redblack t col n: 
t is a red-black tree having n black nodes from any leaf to the root,
and it is legal to put t as a subtree into the child of a new root with color col. *)

Ltac ultimate_tactic := 
      repeat match goal with
      | (* Let's destruct all match's conditions *)
        [ |- context[match ?c with _ => _ end] ] => destruct c

      (* A few rules to find false hypothesis: *)
      | (* is_redblack (T Red _ _ _ (T Red)) _ is impossible. *)
      H: is_redblack (T Red _ _ _ (T Red _ _ _ _)) _ _ |- _ => inv H
      | (* is_redblack (T Red _ _ _ _) Red _ is impossible. *)
      H: is_redblack (T Red _ _ _ _) Red _ |- _ => inv H
      | (*  nearly_redblack E n cannot happen *)
      H: nearly_redblack E _ |- _ => inv H
      | (* is_redblack E _ (S n) cannot happen *)
      H: is_redblack E _ (S _) |- _ => inv H

      (* Then, a few rules for simplification: *)
      | (* If is_redblack E _ n0, n0 is 0 *)
      H: is_redblack E _ ?n0 |- _ => inv H
      | (* If is_redblack _ _ 0, invert it; either it is false or makes splitted hypothesis *)
      H: is_redblack _ _ 0 |- _ => inv H

      (* A few cases where the tree's depth is constant: *)
      | |- nearly_redblack _ 1 => constructor
      | |- is_redblack E _ 0 => apply IsRB_leaf
      | |- is_redblack (T _ _ _ _ _) _ 1 => constructor
      | |- is_redblack _ _ 0 => constructor

      (* Now, observe which goals remain, and add patterns one by one *) 
      | |- nearly_redblack (T _ _ _ _ _) (S _) => constructor
      | |- is_redblack (T _ _ _ _ _) _ (S _) => constructor
      | H: is_redblack (T _ _ _ _ _) _ _ |- _ => inv H
      | H: is_redblack ?a Red ?b |- is_redblack ?a Black ?b => apply is_redblack_toblack
      | H1: nearly_redblack (T _ _ _ _ _) _ |- _ => inv H1
      end.

Lemma ins_is_redblack:
  forall x vx s n,
    (is_redblack s Black n -> nearly_redblack (ins x vx s) n) /\
    (is_redblack s Red n -> is_redblack (ins x vx s) Black n).
Proof.
induction s; intro n; simpl; split; intros; inv H; repeat constructor; auto.
destruct (IHs1 n); clear IHs1.
destruct (IHs2 n); clear IHs2.
specialize (H0 H6).
specialize (H2 H7).
clear H H1.
unfold balance.

{
  bdestruct (ltb x k); bdestruct (ltb k x);
  constructor; try assumption; apply is_redblack_toblack; assumption.
}
{ 
  assert (IHs1' := IHs1 n0). inv IHs1'. clear IHs1.
  assert (IHs2' := IHs2 n0). inv IHs2'. clear IHs2.

  assert (HNR1 := H H7).
  assert (HNR2 := H1 H8).
  bdestruct (ltb x k); bdestruct (ltb k x); try nia; simpl;
    ultimate_tactic; assumption.
}
{
  assert (IHs1' := IHs1 n0). inv IHs1'. clear IHs1.
  assert (IHs2' := IHs2 n0). inv IHs2'. clear IHs2.

  assert (HNR1 := H H7).
  assert (HNR2 := H1 H8).
  bdestruct (ltb x k); bdestruct (ltb k x); try nia; simpl;
    ultimate_tactic; assumption.
}
Qed.
