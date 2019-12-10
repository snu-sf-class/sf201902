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
 

Definition Read (name: string) : StateM nat :=
  (fun s => (s name, s)).

Definition Write (x: string) (v: nat) : StateM unit :=
  (fun s => (tt, updateS s x v)).

Definition summation n : StateM nat :=
  Write "sum" 0;;
  For 0 (n+1) (fun i =>
    sum <- Read "sum";;
    Write "sum" (sum + i)
  );;
  sum <- Read "sum";;
  ret sum
.

Compute (summation 100 : StateM nat).

Compute (runStateM (summation 100)).

(****
  IO Monad
 ****)

Inductive IOM (X: Type) : Type :=
| io_ret (x: X) : IOM X
| io_in (cont: nat -> IOM X) : IOM X
| io_out (n: nat) (cont: IOM X) : IOM X
.
Arguments io_ret {X}.
Arguments io_in {X}.
Arguments io_out {X}.

Fixpoint iobind {X Y} (m: IOM X) (f: X -> IOM Y) :=
  match m with
  | io_ret x => f x
  | io_in cont => io_in (fun n => iobind (cont n) f)
  | io_out n cont => io_out n (iobind cont f)
  end.

Instance IOMonad : Monad IOM :=
  {
    ret X x := io_ret x;
    bind X Y (m: IOM X) (f: X -> IOM Y) := iobind m f;
  }.

Fixpoint runIOM (m: IOM unit) (inputs: list nat) : list nat :=
  match m with
  | io_ret _ => []
  | io_in cont =>
    match inputs with
    | [] => []
    | n::inputs' => runIOM (cont n) inputs'
    end
  | io_out n cont =>
    n :: runIOM cont inputs
  end.

Definition Input : IOM nat :=
  io_in (fun n => io_ret n).

Definition Output (n: nat) : IOM unit :=
  io_out n (io_ret tt).

Fixpoint sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum n'
  end.

Definition sumIO : IOM unit :=
  n <- Input;;
  Output (sum n);;
  m <- Input;;
  Output (sum (n+m)).

Compute runIOM sumIO [10; 10].

(****
  State Monad Transformer
 ****)

Definition StateMT (M: Type -> Type) X := State -> M (X * State)%type.

Instance StateMonadT {M} `{Monad M} : Monad (StateMT M) :=
  {
    ret X x :=
      (fun s => ret (x, s));
    bind X Y (m: StateMT M X) (f: X -> StateMT M Y) :=
      (fun s =>
         xs' <- m s;;
         f (fst xs') (snd xs'));
  }.

Definition runStateMT {M} `{Monad M} {X} (m: StateMT M X) : M X :=
  xs <- m initS;; ret (fst xs).

Definition LiftT {M} `{Monad M} {X} : M X -> StateMT M X :=
  (fun m s => x <- m;; ret (x, s)).

Fixpoint ForT {M} `{Monad M} (b n: nat) (body: nat -> StateMT M unit) : StateMT M unit :=
  match n with
  | 0 => ret tt
  | S n' => body b;;
            ForT (1+b) n' body
  end.

Definition ReadT {M} `{Monad M} (name: string) : StateMT M nat :=
  (fun s => ret (s name, s)).

Definition WriteT {M} `{Monad M} (x: string) (v: nat) : StateMT M unit :=
  (fun s => ret (tt, updateS s x v)).

Definition sumIOSt : StateMT IOM unit :=
  n <- LiftT Input;;
  WriteT "sum" 0;;
  ForT 0 (n+1) (fun i =>
    sum <- ReadT "sum";;
    WriteT "sum" (sum + i)
  );;
  sum <- ReadT "sum";;
  LiftT (Output sum).

Compute (runIOM (runStateMT sumIOSt) [100]).
