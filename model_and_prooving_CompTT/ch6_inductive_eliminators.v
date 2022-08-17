From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem kaminski_equation: forall (f: bool -> bool) x, 
  f (f (f x)) = f x.
Proof.
  move => f x.
  case Eqf: (f x).
  case Eqh: x.
  move: Eqh Eqf => -> Hf.
  by rewrite Hf.
  case Eftrue: (f true).
  by apply Eftrue.
  move: Eqh Eqf => ->.
  by apply.
  case Eqx: x.
  case Eqffalse: (f false).
  move: Eqx Eqf => ->.
  by apply.
  move: Eqx Eqf => -> ftf.
  by apply Eqffalse.
  move: Eqx Eqf => -> H.
  rewrite H.
  by apply H.
Qed.

(* 6.1.3 *)
Lemma pigeon_hole: forall (x y z: bool), x = y \/ x = z \/ y = z.
Proof.
  move => x y z.
  case x; case y; case z; try auto.
Qed.


Theorem kaminski_equation': forall (f: bool -> bool) x, 
  f (f (f x)) = f x.
Proof.
  move => f x.
  case (pigeon_hole (f (f x)) (f x) x).
    move => H.
    by rewrite H H.
  case.
    move => H.
    by rewrite H.
  move => H.
  by rewrite H H H.
Qed.

(* 6.5.1 *)
Goal ~(nat = bool).
Proof.
  move => H.
Admitted.

(* 6.5.2 *)
(* TODO *)

(* 6.7.1 *)
(* TODO *)