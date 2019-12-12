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



