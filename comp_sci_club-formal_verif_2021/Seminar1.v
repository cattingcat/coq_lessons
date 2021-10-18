 
From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:= 
  fun (t : (A * B) * C ) => 
    match t with
    | ((a, b), c) => (a, (b, c))
    end.


Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:=
  fun (t : (A + B) + C) => 
    match t with 
    | inl (inl a) => inl a
    | inl (inr b) => inr (inl b)
    | inr c => inr (inr c)
    end.

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:=
  fun (t : A * (B + C)) =>
    match t with
    | (a, inl b) => inl (a, b)
    | (a, inr c) => inr (a, c)
    end.


Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:=
  fun (t : A + (B * C)) =>
    match t with 
    | inl a => (inl a, inl a)
    | inr (b, c) => (inr b, inr c)
    end.



(* function composition *)
Definition comp {A B C : Type} (f : B -> A) (g : C -> B) : C -> A
:=
  (fun (c : C) => f (g c)).


(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)
Notation "f \o g" := 
  (comp f g)
  (at level 40, left associativity).

(* Introduce empty type, call `void` *)
Inductive void : Type := .
Definition absurd {A: Type} (v : void): A 
:=
  match v with
  end.



(* Definition void_terminal {A : Type} : (void -> A). *)

(* Introduce `unit` type (a type with exactly one canonical form) *)
Inductive unit : Type :=
  | uni.

Definition unit_initial (A : Type) :
  A -> unit
:= fun (a : A) => uni.



(* Think of some more type signatures involving void, unit, sum, prod *)