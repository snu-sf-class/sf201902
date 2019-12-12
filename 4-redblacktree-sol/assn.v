Require Export Coq.Init.Nat.
Require Export Coq.Lists.List.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Omega.
Require Export Perm Extract.
Require Extraction.
Import ListNotations.
Open Scope nat_scope.
Require Export ZArith.
Open Scope Z_scope.
Export IntMaps.


Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Definition key := int.

Inductive color := Red | Black.

Fixpoint map_reduce {A C} (f: A -> C -> C) (c0: C) (l: list A) : C :=
  match l with
  | nil => c0
  | hd::tl => f hd (map_reduce f c0 tl)
  end.

Variable V : Type.
Variable default: V.

Inductive tree  : Type :=
| E : tree
| T: color -> tree -> key -> V -> tree -> tree.

Definition empty_tree := E.

Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T _ tl k v tr => if ltb x k then lookup x tl
                         else if ltb k x then lookup x tr
                         else v
  end.

Definition balance rb t1 k vk t2 :=
 match rb with Red => T Red t1 k vk t2
 | _ =>
 match t1 with
 | T Red (T Red a x vx b) y vy c =>
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | T Red a x vx (T Red b y vy c) =>
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | a => match t2 with
            | T Red (T Red b y vy c) z vz d =>
	        T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | T Red b y vy (T Red c z vz d)  =>
	        T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | _ => T Black t1 k vk t2
            end
  end
 end.

Definition makeBlack t :=
  match t with
  | E => E
  | T _ a x vx b => T Black a x vx b
  end.

Fixpoint ins x vx s :=
 match s with
 | E => T Red E x vx E
 | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                        else if ltb y x then balance c a y vy (ins x vx b)
                        else T c a x vx b
 end.

Definition insert x vx s := makeBlack (ins x vx s).

Inductive SearchTree' : Z -> tree -> Z -> Prop :=
| ST_E : forall lo hi, lo <= hi -> SearchTree' lo E hi
| ST_T: forall lo c l k v r hi,
    SearchTree' lo l (int2Z k) ->
    SearchTree' (int2Z k + 1) r hi ->
    SearchTree' lo (T c l k v r) hi.

Inductive SearchTree: tree -> Prop :=
| ST_intro: forall t lo hi, SearchTree' lo t hi -> SearchTree t.

Definition combine {A} (pivot: Z) (m1 m2: total_map A) : total_map A :=
  fun x => if Z.ltb x pivot  then m1 x else m2 x.

Inductive Abs:  tree -> total_map V -> Prop :=
| Abs_E: Abs E (t_empty default)
| Abs_T: forall a b c l k vk r,
      Abs l a ->
      Abs r b ->
      Abs (T c l k vk r)  (t_update (combine (int2Z k) a b) (int2Z k) vk).

Theorem empty_tree_relate: Abs empty_tree (t_empty default).
Proof.
constructor.
Qed.

Lemma balance_SearchTree:
 forall c  s1 k kv s2 lo hi,
   SearchTree' lo s1 (int2Z k) ->
   SearchTree' (int2Z k + 1) s2 hi ->
   SearchTree' lo (balance c s1 k kv s2) hi.
Proof.
intros.
unfold balance.

(** Use proof automation for this case analysis. *)

repeat  match goal with
  | |- SearchTree' _ (match ?c with Red => _ | Black => _ end) _ =>
              destruct c
  | |- SearchTree' _ (match ?s with E => _ | T _ _ _ _ _ => _ end) _ =>
              destruct s
  | H: SearchTree' _ E _   |- _  => inv H
  | H: SearchTree' _ (T _ _ _ _ _) _   |- _  => inv H
  end;
 repeat (constructor; auto).
Qed.

(** The relation [is_redblack] ensures that there are exactly [n] black
   nodes in every path from the root to a leaf, and that there are never
   two red nodes in a row. *)

Inductive is_redblack : tree -> color -> nat -> Prop :=
| IsRB_leaf: forall c, is_redblack E c 0
| IsRB_r: forall tl k kv tr n,
        is_redblack tl Red n ->
        is_redblack tr Red n ->
        is_redblack (T Red tl k kv tr) Black n
| IsRB_b: forall c tl k kv tr n,
        is_redblack tl Black n ->
        is_redblack tr Black n ->
        is_redblack (T Black tl k kv tr) c (S n).

(** [nearly_redblack] expresses, "the tree is a red-black tree, except that
it's nonempty and it is permitted to have two red nodes in a row at
the very root (only)."   *)

Inductive nearly_redblack : tree -> nat -> Prop :=
| nrRB_r: forall tl k kv tr n,
       is_redblack tl Black n ->
       is_redblack tr Black n ->
       nearly_redblack (T Red tl k kv tr) n
| nrRB_b: forall tl k kv tr n,
       is_redblack tl Black n ->
       is_redblack tr Black n ->
       nearly_redblack (T Black tl k kv tr) (S n).

Lemma makeBlack_relate:
forall t cts,
  Abs t cts ->
  Abs (makeBlack t) cts.
Proof.
intros.
destruct t; simpl; auto.
inv H; constructor; auto.
Qed.


Lemma SearchTree'_le:
  forall lo t hi, SearchTree' lo t hi -> lo <= hi.
Proof.
induction 1; omega.
Qed.

Lemma expand_range_SearchTree':
  forall s lo hi,
   SearchTree' lo s hi ->
   forall lo' hi',
   lo' <= lo -> hi <= hi' ->
   SearchTree' lo' s hi'.
Proof.
induction 1; intros.
constructor.
omega.
constructor.
apply IHSearchTree'1; omega.
apply IHSearchTree'2; omega.
Qed.



(*=========== 3141592 ===========*)

(** **** Exercise: 2 stars (ins_SearchTree)  *)
(** This one is pretty easy, even without proof automation.
  Copy-paste your proof of insert_SearchTree from Extract.v.
  You will need to apply [balance_SearchTree] in two places.
 *)
 Lemma ins_SearchTree:
 forall x vx s lo hi,
                  lo <= int2Z x ->
                  int2Z x < hi ->
                  SearchTree' lo s hi ->
                  SearchTree' lo (ins x vx s) hi.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)
Check ins_SearchTree:  forall x vx s lo hi,
lo <= int2Z x ->
int2Z x < hi ->
SearchTree' lo s hi ->
SearchTree' lo (ins x vx s) hi.


(*=========== 3141592 ===========*)

Lemma empty_tree_SearchTree: SearchTree empty_tree.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)
Check empty_tree_SearchTree: SearchTree empty_tree.


(*=========== 3141592 ===========*)

(* You can use SearchTree'_le, expand_range_SearchTree'. *)
Lemma insert_SearchTree: forall x vx s,
    SearchTree s -> SearchTree (insert x vx s).
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)
Check insert_SearchTree: forall x vx s, SearchTree s -> SearchTree (insert x vx s).


(*=========== 3141592 ===========*)

Theorem lookup_relate:
  forall k t cts ,   Abs t cts -> lookup k t =  cts (int2Z k).
Proof.  (* Copy your proof from Extract.v, and adapt it. *)
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)
Check lookup_relate:  forall k t cts ,   Abs t cts -> lookup k t =  cts (int2Z k).


(*=========== 3141592 ===========*)

(** **** Exercise: 4 stars (balance_relate)  *)
(** You will need proof automation for this one.  Study the methods used
  in [ins_not_E] and [balance_SearchTree], and try them here.
  Add one clause at a time to your [match goal]. *)
Lemma Abs_helper:
  forall m' t m, Abs t m' ->    m' = m ->     Abs t m.
Proof.
   intros. subst. auto.
Qed.

Ltac contents_equivalent_prover :=
 extensionality x; unfold t_update, combine, t_empty;
 repeat match goal with
  | |- context [if ?A then _ else _] => bdestruct A
 end;
 auto;
 omega.

Theorem balance_relate:
  forall c l k vk r m,
    SearchTree (T c l k vk r) ->
    Abs (T c l k vk r) m ->
    Abs (balance c l k vk r) m.
Proof.
intros.
inv H.
unfold balance.
repeat match goal with
 | H: Abs E _ |- _ => inv H
end.
(** Add these clauses, one at a time, to your [repeat match goal] tactic,
   and try it out:
   -1. Whenever a clause [H: Abs E _] is above the line, invert it by [inv H].
             Take note: with just this one clause, how many subgoals remain?
   -2. Whenever [Abs (T _ _ _ _ _) _] is above the line, invert it.
             Take note: with just these two clause, how many subgoals remain?
   -3. Whenever [SearchTree' _ E _] is above the line, invert it.
             Take note after this step and each step: how many subgoals remain?
   -4. Same for [SearchTree' _ (T _ _ _ _ _) _].
   -5. When [Abs match c with Red => _ | Black => _ end _] is below the line,
          [destruct c].
   -6. When [Abs match s with E => _ | T ... => _ end _] is below the line,
          [destruct s].
   -7. Whenever [Abs (T _ _ _ _ _) _] is below the line,
                  prove it by [apply Abs_T].   This won't always work;
         Sometimes the "cts" in the proof goal does not exactly match the form
         of the "cts" required by the [Abs_T] constructor.  But it's all right if
         a clause fails; in that case, the [match goal] will just try the next clause.
          Take note, as usual: how many clauses remain?
   -8.  Whenever [Abs E _] is below the line, solve it by [apply Abs_E].
   -9.  Whenever the current proof goal matches a hypothesis above the line,
          just use it.  That is, just add this clause:
       | |- _ => assumption
   -10.  At this point, if all has gone well, you should have exactly 21 subgoals.
       Each one should be of the form, [  Abs (T ...) (t_update...) ]
       What you want to do is replace (t_update...) with a different "contents"
       that matches the form required by the Abs_T constructor.
       In the first proof goal, do this: [eapply Abs_helper].
       Notice that you have two subgoals.
       The first subgoal you can prove by:
           apply Abs_T. apply Abs_T. apply Abs_E. apply Abs_E.
           apply Abs_T. eassumption. eassumption.
       Step through that, one at a time, to see what it's doing.
       Now, undo those 7 commands, and do this instead:
            repeat econstructor; eassumption.
       That solves the subgoal in exactly the same way.
       Now, wrap this all up, by adding this clause to your [match goal]:
       | |- _ =>  eapply Abs_helper; [repeat econstructor; eassumption | ]
   -11.  You should still have exactly 21 subgoals, each one of the form,
             [ t_update... = t_update... ].  Notice above the line you have some
           assumptions of the form,  [ H: SearchTree' lo _ hi ].  For this equality
         proof, we'll need to know that [lo <= hi].  So, add a clause at the end
        of your [match goal] to apply SearchTree'_le in any such assumption,
        when below the line the proof goal is an equality [ _ = _ ].
   -12.  Still exactly 21 subgoals.  In the first subgoal, try:
          [contents_equivalent_prover].   That should solve the goal.
          Look above, at [Ltac contents_equivalent_prover], to see how it works.
          Now, add a clause to  [match goal] that does this for all the subgoals.

   -Qed! *)
exact FILL_IN_HERE. Qed.

(*-- Check --*)
Check balance_relate:
  forall c l k vk r m,
    SearchTree (T c l k vk r) ->
    Abs (T c l k vk r) m ->
    Abs (balance c l k vk r) m.


(*=========== 3141592 ===========*)

Theorem ins_relate:
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (ins k v t) (t_update cts (int2Z k) v).
Proof. exact FILL_IN_HERE. Qed.

Theorem insert_relate:
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (insert k v t) (t_update cts (int2Z k) v).
Proof.
intros.
unfold insert.
apply makeBlack_relate.
apply ins_relate; auto.
Qed.

(** * Final Correctness Theorem *)

Theorem redblack_correct: forall (l: list (key*V)) k,
  lookup k (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree l) =
           (map_reduce (fun kv tm => t_update tm (int2Z (fst kv)) (snd kv)) (t_empty default) l) (int2Z k).
Proof.
  assert (ABS: forall l,
     SearchTree (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree l) /\
     Abs (map_reduce (fun kv tr => insert   (fst kv) (snd kv) tr) empty_tree l)
         (map_reduce (fun kv tm => t_update tm (int2Z (fst kv)) (snd kv)) (t_empty default) l)).
  { intros. induction l; simpl.
    - eauto using empty_tree_SearchTree, empty_tree_relate.
    - destruct IHl.
      eauto using insert_SearchTree, insert_relate.
  }
  intros. eapply lookup_relate, ABS.
Qed.

(*-- Check --*)

Check ins_relate:
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (ins k v t) (t_update cts (int2Z k) v).


(*=========== 3141592 ===========*)

Lemma is_redblack_toblack:
  forall s n, is_redblack s Red n -> is_redblack s Black n.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check is_redblack_toblack:
  forall s n, is_redblack s Red n -> is_redblack s Black n.


(*=========== 3141592 ===========*)

Lemma makeblack_fiddle:
  forall s n, is_redblack s Black n ->
            exists n, is_redblack (makeBlack s) Red n.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check makeblack_fiddle:
  forall s n, is_redblack s Black n ->
            exists n, is_redblack (makeBlack s) Red n.


(*=========== 3141592 ===========*)

Lemma ins_is_redblack:
  forall x vx s n,
    (is_redblack s Black n -> nearly_redblack (ins x vx s) n) /\
    (is_redblack s Red n -> is_redblack (ins x vx s) Black n).
Proof.
exact FILL_IN_HERE. Qed.
(*
induction s; intro n; simpl; split; intros; inv H; repeat constructor; auto.
destruct (IHs1 n); clear IHs1.
destruct (IHs2 n); clear IHs2.
specialize (H0 H6).
specialize (H2 H7).
clear H H1.
unfold balance. *)
(** You will need proof automation, in a similar style to
   the proofs of [ins_not_E] and [balance_relate]. *)

(*-- Check --*)

Check ins_is_redblack:
  forall x vx s n,
    (is_redblack s Black n -> nearly_redblack (ins x vx s) n) /\
    (is_redblack s Red n -> is_redblack (ins x vx s) Black n).


(*=========== 3141592 ===========*)

Lemma insert_is_redblack:
  forall x xv s n, is_redblack s Red n ->
                    exists n', is_redblack (insert x xv s) Red n'.
Proof.
Proof.   (* Just apply a couple of lemmas:
    ins_is_redblack and makeblack_fiddle *)
exact FILL_IN_HERE. Qed.

Hint Constructors is_redblack.
Theorem redblack_efficient: forall (l: list (key*V)),
    exists n, is_redblack (map_reduce (fun kv tr => insert (fst kv) (snd kv) tr) empty_tree l) Red n.
Proof.
  induction l.
  - eauto.
  - destruct IHl.
    eapply insert_is_redblack; eauto.
Qed.

(*-- Check --*)

Check insert_is_redblack:
  forall x xv s n, is_redblack s Red n ->
                    exists n', is_redblack (insert x xv s) Red n'.
