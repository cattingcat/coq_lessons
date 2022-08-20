From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive ex (T : Type) (p: T -> Prop): Prop := 
  | ex_intro (x: T) of p x.

Definition M_ex: forall (X: Type) (P: X -> Prop) (Z: Prop), ex P -> (forall x, P x -> Z) -> Z :=
  fun X P Z e f =>
    match e with 
    | ex_intro x px => f x px
    end.

(* 8.1.1 *)
Goal forall T K (p: T -> K -> Prop), (exists x y, p x y) -> (exists y x, p x y).
Proof.
  move => T K p.
  move => [x [y pxy]].
  exists y.
  exists x.
  apply pxy.
Qed.


Goal forall T (p: T -> Prop), (exists x, p x) -> ~(forall x, ~ (p x)).
Proof.
  move => T P [x px] H.
  by apply (H x px).
Qed.

(* 8.1.3 *)
Goal forall T (x y : T), ~(x = y) -> exists p, p x /\ ~(p y).
Proof.
  move => T x y Hneq.
  exists (fun a => a = x).
  split.
    done.
  move => H.
  apply Hneq.
  by rewrite H.
Qed.

(* 8.2.1 *)
Lemma russel_lemma: forall (P: Prop), ~(P <-> ~P).
Proof.
  move => P [H H'].
  apply H.
    apply H'.
    move => p.
    apply H.
      apply p.
      apply p.
  apply H'.
  move => p.
  apply H.
    apply p.
    apply p.
Qed.

Theorem barber_theorem: forall (X : Type) (P: X -> X -> Prop),
  ~(exists x, forall y, P x y <-> ~(P y y)).
Proof.
  move => X P [x H].
  set Hx := H x.
  apply (russel_lemma Hx).
Qed.


Definition FixedPoint T (x: T) (f: T -> T) := f x = x.

Lemma negb_no_fp: ~ (exists x, FixedPoint x negb).
Proof.
  move => [x].
  case x.
  - by rewrite /FixedPoint /=.
  by rewrite /FixedPoint /=.
Qed.

Lemma neg_prop_no_fp: ~ (exists P, FixedPoint P (fun x => ~x)).
Proof.
  move => [x].
  rewrite /FixedPoint => P.
  apply (@russel_lemma x).
  by rewrite P.
Qed.

Definition surjective T K (f: T -> K) := forall (k: K), exists (t: T), f t = k.

Theorem lawvere X Y: 
  (exists (f : X -> (X -> Y)), surjective f) -> 
    forall (g: Y -> Y), exists x, FixedPoint x g.
Proof.
  rewrite /surjective /FixedPoint.
  move => [f sf] g.
  set tmp := sf (fun x => g(f x x)).
  move : tmp => [a H].
  exists (f a a).
  by rewrite {2}H.
Qed.

(* 8.3.4 *)
Corollary t_834 X: ~(exists (f: X -> (X -> bool)), surjective f).
Proof.
  move => H.
  apply negb_no_fp.
  apply (@lawvere X bool).
  by apply H.
Qed.

(* 8.3.5 *)
Corollary t_835 X: ~(exists (f: X -> (X -> Prop)), surjective f).
Proof.
  move => H.
  apply neg_prop_no_fp.
  apply (@lawvere X Prop).
  by apply H.
Qed.
