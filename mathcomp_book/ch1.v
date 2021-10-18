(* nix-shell --packages coq coqPackages.mathcomp coqPackages.QuickChick *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition f0 := fun n => n + 1.
Definition f1 n := n + 1.
Definition f2 (n: nat) : nat := n + 1.
Definition f3 : nat -> nat := fun n => n + 1.

About f0.
Print f0.
Check f0.
Check f0 0.
Fail Check f0 (fun x => x + 1).
Compute f0 1.

Compute 
  let n := 33 in
  let e := n + n + n in
    e + e + e.

Check fun n => f0 n.+1.

Search ".+1".

Definition non_zero n := if n is _.+1 then true else false.

Check 1 :: 2 :: 3 :: nil.
About seq.

Check fun l => 1 :: 2 :: 3 :: l.

Check fun l : seq nat => [:: 1, 2, 3 & l].


Record poin := Point { x: nat; y: nat; z: nat }.

Compute x (Point 1 2 3).
Compute (Point 1 2 3).(x).
About x.


Section iterators.
  Variables (T: Type) (A: Type).
  Variable (f: T -> A -> A).

  Implicit Type x : T.
  Implicit Type n : nat.

  Fixpoint iter n op x :=
    if n is p.+1 then op (iter p op x) else x.

  Check iter.

  Fixpoint foldr a s :=
    if s is y :: ys then f y (foldr a ys) else a.
End iterators.

Check foldr.


Section tst.
  Variables (T A : Type).
  Variable (t: nat -> Type).
  Variable qwe : forall n, t n.
  Definition tstFunc (a: nat) : nat -> t a := fun _ => qwe a.
End tst.
About tstFunc.

(*Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s).*)
Compute [seq i.+1 | i <- [:: 2; 3]].

Eval simpl in predn (addn 0.+1 7).


About addnA.
About cancel.
Print rel.
Print pred.
Print commutative.


Inductive my_conj (A B C D: Prop) :=
  | mconj of A & B & C & D.
Print my_conj.



