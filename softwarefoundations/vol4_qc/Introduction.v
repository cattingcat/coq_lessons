Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

(* nix-shell --packages coq coqPackages.mathcomp coqPackages.QuickChick *)

From QuickChick Require Import QuickChick.
Require Import List ZArith. Import ListNotations.



Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | h::t => if h =? x then t else h :: remove x t
  end.

Conjecture removeP : forall x l, ~ (In x (remove x l)).

QuickChick removeP.



Fixpoint removeAll (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | h::t => if h =? x then removeAll x t else h :: removeAll x t
  end.

Conjecture removeAllP : forall x l, ~ (In x (removeAll x l)).

QuickChick removeAllP.



Fixpoint insert x l :=
  match l with
  | []   => [x]
  | y::t => if y <? x then y :: insert x t else x :: y :: t
  end.

Conjecture insertP : forall x l, In x (insert x l).

QuickChick insertP.



Conjecture insertYP : forall x y l, In y l -> In y (insert x l).

QuickChick insertYP.