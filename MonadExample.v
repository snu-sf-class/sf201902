(***
To successfully run this example, you need to install CoqExtLib.

This will work:

  cd ~
  git clone git@github.com:coq-community/coq-ext-lib.git --branch=v8.9
  cd coq-ext-lib
  make
  make install
***)

Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Omega.
Require Import List. Import ListNotations.
Local Open Scope string.

Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

(****
  State Monad
 ****)

Definition State := string -> nat.

Definition StateM X := State -> (X * State).

Definition initS : State :=
  (fun y => 0).

Definition updateS (s: State) (x: string) (v: nat) : State :=
  (fun y => if String.eqb x y then v else s x).

Instance StateMonad : Monad StateM :=
  {
    ret X x :=
      (fun s => (x, s));
    bind X Y (m: StateM X) (f: X -> StateM Y) :=
      (fun s =>
         let (x,s') := m s in
         f x s');
  }.

Definition runStateM {X} (m: StateM X) : X :=
  fst (m initS).

Fixpoint For (b n: nat) (body: nat -> StateM unit) : StateM unit :=
  match n with
  | 0 => ret tt
  | S n' => body b;;
