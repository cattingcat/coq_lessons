From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition fun_ext := forall X (P: X -> Prop) (f g : forall x, P x), 
  (forall x, f x = g x) -> f = g.

Definition prop_ext := forall P Q, P <-> Q -> P = Q.

Definition proof_irrelevance := forall (Q: Prop) (a b : Q), a = b.


(* 12.2 Set extensionality *)
Definition empty_set X := { x: X & False }.

Definition diff X (p g: X -> Prop) (a: {x | p x}) (b: {x | g x}) := {x | p x /\ ~(g x)}.

Definition diff' X (p g: X -> Prop) := fun x => p x /\ ~(g x).

Lemma tst: forall X (x: X) (p g: X -> Prop), diff' p g x -> p x /\ ~ (g x).
Proof.
  move => X x p g H.
  case: H.
  by [].
Qed.

(* 12.3 Proof irrelevance *)
Definition unique (X: Type) := forall (x y : X), x = y.

  (* proof_irrelevance in unique, all proofs are irrelevent *)
Lemma pi_up: forall Q: Prop, proof_irrelevance -> unique Q.
Proof.
  rewrite /proof_irrelevance /unique.
  move => Q pi x y.
  by apply (pi Q).
Qed.

Lemma e1: unique True.
Proof. move => x y. by case x; case y. Qed.