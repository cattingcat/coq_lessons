From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "exists".

(* 10.1.1 *)
(* Coq.Init.Logic - Props*)
Lemma tst_prop: forall x, exists n, x = n * 2 \/ x = S(n * 2).
Proof.
  elim => [| x [n IH]].
    exists 0. by left.
  case IH.
    move => H.
    exists n.
    right.
    by rewrite -H.
  move => H.
  exists (S n).
  left.
  by rewrite mulSn 2!addSn add0n -H.
Defined.

Compute (tst_prop 5).

(* Coq.Init.Specif - various options arount sigma types *)
Lemma tst_type: forall x,  { n & {x = n * 2} + {x = S(n * 2)} }.
Proof.
  elim => [| x [n IH]].
    exists 0. by left.
  case IH.
    move => H.
    exists n.
    right.
    by rewrite -H.
  move => H.
  exists (S n).
  left.
  by rewrite mulSn 2!addSn add0n -H.
Defined.

Compute (tst_type 5).

Definition tst (n: nat): nat :=
  match (tst_type n) with
  | existT a b => a
  end.

Definition is_even (n: nat): bool := 
  match (tst_type n) with
  | existT a (left _) => true
  | existT a (right _) => false
  end.

Compute (tst 6).
Compute (is_even 6).

(* Prop in calculation *)
Fail Definition tst_prop (n: nat): nat :=
  match (tst_prop n) with
  | ex_intro a b => a
  end.


Locate "+".
Print sumor.
Print sumbool.
Print sum.

(* 10.2.5 *)
Definition e1: forall b, (b = true) + (b = false) := 
  fun b =>
    match b with
    | true => inl erefl
    | false => inr erefl
    end.

Definition e2: forall n, (n = 0) + ({n' & n = S n'}) :=
  fun n =>
    match n return (n = 0) + ({n' & n = S n'}) with 
    | 0 => inl erefl
    | S n' as n => inr (existT (fun x => n = S x) n' (erefl (S n')))
    end.

Print prod.
Search ((_ -> _) * (_ -> _)).
Search (Type -> Type -> Prop).

(* 10.2.8 *)
(* Lemma sigma_bij X (p : X -> Prop): { x & p x } <-> (forall Z, (forall x, p x -> Z) -> Z). *)

(* 10.2.9 *)
Lemma sigma_eq_fw X Y : X + Y -> { b & if b then X else Y }.
Proof.
  case.
    by exists true.
  by exists false.
Defined.

Lemma sigma_eq_bw X Y : { b & if b then X else Y } -> X + Y.
Proof.
  move => [b p].
  case: b p => H.
    by left.
  by right.
Defined.

(* 10.3 *)
Definition p1 X (p: X -> Type): {x & p x} -> X :=
  fun p =>
    match p with
    | existT x p => x
    end.

Definition p2 X (p: X -> Type): forall (a: {x & p x}), p (p1 a) :=
  fun a =>
    match a with
    | existT x p' => p'
    end.

(* 10.3.1 *)
Lemma scolem_fw (X Y: Type) (p: X -> Y -> Type): 
  (forall x, { y & p x y}) -> { f & forall x, p x (f x) }.
Proof.
  move => H.
  exists (fun x => p1 (H x)).
  move => x.
  move : (H x) => hx.
  case : hx => [y pxy].
  by rewrite /p1.
Defined.

Lemma scolem_bw (X Y: Type) (p: X -> Y -> Type): 
   { f & forall x, p x (f x) } -> forall x, { y & p x y}.
Proof.
  move => [f H] x.
  exists (f x).
  by apply (H x).
Defined.
