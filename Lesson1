From mathcomp Require Import ssreflect.

Module Lesson1.

Inductive bool : Type := 
| true
| false.

Check false : bool.
Check false.

Check bool : Type.
Check (bool -> bool) : Type.
Check (fun (b : bool) => b) : (bool -> bool). (* Lambda  id *)
Check (fun t: Type => t): (Type -> Type).
Check ((fun t: Type => t) bool): Type.

Check (fun b => b).

Check ((fun b => b) true).

Check (fun (f : bool -> bool) => f true).

Compute (fun b : bool => b) true.


Definition idb := (fun b : bool => b).

Check idb.
Check idb true : bool.
Check (fun (f : bool -> bool) => f true) idb.

Fail Check (fun (f : bool -> bool) => f true) false.



Definition negb :=
  fun (b: bool) =>
    match b with
    | true => false
    | false => true
    end.

Check negb true : bool.

(* cbv - call by value *)
Eval cbv beta delta in negb true.

Variable c : bool.

Compute negb c.


Definition andb (b c : bool) : bool :=
  match b with
  | false => false
  | true => c
  end.

Definition andb' (b c : bool) : bool :=
  match c with
  | false => false
  | true => b
  end.

Definition orb (b c : bool) : bool :=
  match b with 
  | true => true
  | false => c
  end.

Compute orb true false.
Compute orb false false.
Compute orb false true.


Definition eqb (b c : bool) : bool := 
  match (b, c) with 
  | (true, true) => true
  | (false, false) => true
  | (_, _) => false
  end.







Inductive nat : Type :=
| Z
| S of nat. (* 'of' taken from ssreflect, S : nat -> nat*)

Inductive nat2 : Type :=
| Z2 : nat2
| S2 : nat2 -> nat2.


Check S Z.

Definition succn := S.

Compute succn (S Z).


Definition predn' (n : nat) : nat :=
  match n with 
  | S m => m
  | Z => Z
  end.

(*
  Definition predn : forall n : nat, (n <> Z) -> nat := 
    match n with 
    | S m => m
    | Z => Z
    end.
*)

(* {struct n} indicates which parameter recursion run on *)
Fixpoint addn (n m : nat) {struct n} : nat :=
  match n with 
  | Z => m
  | S n' => S (addn n' m)
  end.

Compute addn (S Z) (S Z).

Fixpoint addn' (n m : nat) : nat :=
  if n is S n' then S (addn' n' m) else m.

Definition addn_no_sugar := 
  fix addn (n m : nat) {struct n} : nat :=
    match n with 
    | Z => m
    | S n' => S (addn n' m)
    end.


Fail Fixpoint addn_loop (n m : nat) {struct n} : nat :=
  if n is S n' then addn_loop n m else m.

Fixpoint is_even (n : nat) : bool := 
  if n is S n' then is_odd n' else true
with is_odd (n : nat) : bool := 
  if n is S n' then is_even n' else false.

Compute is_even (S (S (S Z))).
Compute is_even (S (S Z)).
Compute is_odd (S (S (S Z))).
Compute is_odd (S (S Z)).

Definition dec2 (n : nat) : nat :=
  match n with 
  | S (S n') => n'
  | _ => Z
  end.

Compute dec2 (S(S(S(Z)))).
Compute dec2 (S(S Z)).
Compute dec2 (S Z).


Fixpoint subn (m n : nat) {struct m} : nat :=
  match (m, n) with
  | (m, Z) => m
  | (Z, n) => Z
  | (S m', S n') => subn m' n'
  end.

Compute subn Z Z.
Compute subn (S Z) Z.
Compute subn (S Z) (S Z).
Compute subn (S (S Z)) (S Z).
Compute subn (S Z) (S (S Z)).

Fixpoint muln (m n : nat) : nat :=
  match n with 
  | Z => Z
  | S Z => m
  | S n' => addn m (muln m n')
  end.

Compute muln Z Z.
Compute muln (S Z) Z.
Compute muln (S Z) (S Z).
Compute muln (S (S Z)) (S Z).
Compute muln (S (S Z)) (S (S Z)).

Fixpoint leq (m n : nat) : bool :=
  match (m, n) with
  | (Z, Z) => true
  | (Z, _) => true
  | (_, Z) => false
  | (S m', S n') => leq m' n'
  end.

Compute leq Z Z.
Compute leq (S Z) Z.
Compute leq (S Z) (S Z).
Compute leq (S (S Z)) (S Z).
Compute leq (S (S Z)) (S (S Z)).
Compute leq (S Z) (S (S Z)).

Fixpoint divn_helper (m n rest acc: nat) {struct m} : nat := 
  match (m, rest) with
  | (S m', S Z) => divn_helper m' n n (S acc)
  | (S m', S rest') => divn_helper m' n rest' acc
  | (S _, Z) => Z
  | (Z, Z) => S acc
  | (Z, _) => acc
  end.

Definition divn (m n : nat) : nat :=
  divn_helper m n n Z.

Compute divn (S (S Z)) (S Z).


End Lesson1.


