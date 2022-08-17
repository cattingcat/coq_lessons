From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* 5.1.1 *)
Goal ~True -> False.
Proof.
  by apply.
Qed.

(* 5.1.2 *)
Lemma rewrite_law (X: Type): forall (x y: X) (p: X -> Prop), x = y -> p x = p y.
Proof.
  by move => x y p ->.
Qed.

(* 5.2.3 *)
Lemma pair_destr (X: Type): forall (x y x' y': X), (x, y) = (x', y') -> x = x' /\ y = y'.
Proof.
  move => x y x' y'.
  by case.
Qed.

(* 5.2.5 *)
Lemma dis_eq (X: Type): forall (p: X -> Prop) (x y: X), p x -> ~ p y -> ~(x = y).
Proof.
  move => p x y px npy H.
  apply npy.
  rewrite -H.
  by apply px.
Qed.

(* 5.5.1 *)
Lemma f_eq: forall x y, S x = S y -> x = y.
Proof.
  move => x y; by case.
Qed.

(* 5.5.2 *)
Goal forall x, 0 = S x -> True -> False.
Proof.
  move => x. by [].
Qed.
  
(* 5.5.3 *)
Goal forall (X Z : Type) (f g : X -> Z) (x: X), f = g -> f x = g x.
Proof.
  by move => X Z f g x ->.
Qed.

Definition qwe
 (X Z : Type) (f g : X -> Z) (x: X) (refl: f = g): f x = g x :=
  match refl with
  | erefl => erefl (f x) 
  end.