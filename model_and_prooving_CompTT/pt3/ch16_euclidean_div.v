From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* relation x / (s y) *)
Definition  d (x y a b: nat) := (x = a * (S y) + b) /\ b <= y.
(* a - quotient *)
(* b - remainder *)

(* 16.1.1 *)
Lemma d1: forall y, d 0 y 0 0.
Proof.
  split.
    by [].
  by [].
Qed.

Lemma d2: forall x y a b, d x y a b -> b = y -> d (S x) y (S a) 0.
Proof.
  move => x y a b H E.
  move: E H ->.
  rewrite /d.
  move => [Hl Hr].
  split; last by done.
  by rewrite Hl -addnS mulSn addn0 addnC.
Qed.

Lemma d3: forall x y a b, d x y a b -> b <> y -> d (S x) y a (S b).
Proof.
  move => x y a b [Hl Hr] Neq.
  split; last first.
    move: Hr.
    rewrite leq_eqVlt; move => /orP; case; last by done.
      move => /eqP Contra.
      exfalso; apply (Neq Contra).
  by rewrite Hl addnS.
Qed.

(* 16.1.2 *)
Theorem cert_div: forall x y, { ' (a, b) & d x y a b }.
Proof.
  elim => [ y | x' IH y].
    exists (0, 0).
    apply d1.
  set U := IH y.
  move: (IH y) => [[a b] [Hl Hr]].
  move: Hr.
  case: (ltngtP b y) => //.
    move => Lby _.
    exists (a, (S b)).
    apply d3.
    split => //.
      apply (ltnW Lby).
    move => contra.
    move: Lby.
    rewrite contra /(_ < _) subSn.
    rewrite subnn.
    apply /eqP. by [].
      by [].
  move => H _.
  exists ((S a), 0).
  apply (d2 (b:=b)) => //.
  split => //.
  by rewrite H.
Qed.
