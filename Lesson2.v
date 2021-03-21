From mathcomp Require Import ssreflect ssrbool ssrnat.

Module Lesson2.

Print addb.
About addb.
About nat.
Check 42.
Check (S (S (S O))).


Set Printing All.
Check 5 + 4.
Unset Printing All.



Locate ".+1".
Check 2 .+1.

Locate "_ + _".


Fail Definition id : A -> A := fun (a : A) => a.

Definition id : 
  forall A: Type, A -> A 
:= 
  fun A: Type => fun (a : A) => a.

Compute (id nat 42).


Definition id' : 
  forall A: Type, forall x : A, A 
:= 
  fun A: Type => fun (a : A) => a.



Inductive gadt : Type -> Type := 
| gadt_nat : gadt nat
| gadt_bool : gadt bool.

Definition id'' : 
  forall A : Type, gadt A -> A -> A
:=
  fun (A: Type) => fun (g: gadt A) =>
    match g with 
    | gadt_nat  => fun a => a + 1
    | gadt_bool => fun a => negb a
    end.

About not.

Inductive prodn : Type := 
  | pairn of nat & nat.

Print prodn.
(* divmod : nat -> nat -> prodn *)

Inductive prod (A B : Type) : Type :=
  | pair of A & B.

Fail Check prod: Type.
Check prod nat nat: Type.

Check pair : forall A B : Type, A -> B -> prod A B.

Check pair nat bool 42 true.


(* implicit args *)
Arguments id [A] _.
Arguments pair [A B] _ _.

(* Now we can use id without type params *)
Check (id 42).
Compute (id 42).

Compute (pair 42 true).
Compute (@pair _ _ 42 true). (* Original pair with holes for type deduction *)


Notation "A * B" :=
  (prod A B)
  (at level 40, left associativity)
  : type_scope.

Notation "( p ; b )" := (pair p b).

(* Recursive notation *)
Notation "( p , q , .. , r )" := 
  (pair .. (pair p q) .. r) : core_scope.

Check (42, 42, true).

Fail Check nat * bool. (* which * use? *)
Check (nat * bool)%type. (* use * fron type scope *)

Definition fst : forall A B : Type, A * B -> A :=
  fun (A: Type) => fun (B: Type) => fun (p: A * B) =>
    match p with
    | ( a ; _ ) => a
    end.
Arguments fst [A B] _.

Definition snd {A B : Type} : A * B -> B :=
  fun (p: A * B) =>
    match p with
    | (_ ; b) => b
    end.

(*
Notation "p .1" := (fst p).
Notation "p .2" := (snd p).
*)


Compute fst (pair 42 false).

Set Implicit Arguments. (* make implicit args when possible *)


Open Scope type_scope.
Check nat * bool.
Close Scope type_scope.


Definition swap {A B: Type} : A * B -> B * A :=
  fun p =>
    match p with 
    | (a, b) => (b, a)
    end.




Inductive sum (A B: Type) : Type :=
  | inl of A
  | inr of B.
Arguments inl [A B] _.
Arguments inr [A B] _.

Notation "A + B" :=
  (sum A B) (at level 50, left associativity)
  : type_scope.

Definition swap_sum {A B: Type} : A + B -> B + A :=
  fun s =>
    match s with
    | inl a => inr a
    | inr b => inl b
    end.



End Lesson2.