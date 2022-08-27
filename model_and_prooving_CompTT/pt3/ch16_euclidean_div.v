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

Lemma tst: forall n m k, n = m.+1 + k -> m < n.
Proof.
  elim => [m k H | n IH m k].
    exfalso; move: H.
    rewrite addSn.
    by [].
  rewrite addSn. move /eq_add_S ->.
  by rewrite /(_ < _) subSS subnDA subnn sub0n.
Qed.
  
(* 16.3.1 / 16.3.2 *)
Theorem cert_div_unique: forall (x y a b a' b': nat), 
  d x y a b -> d x y a' b' -> a = a' /\ b = b'.
Proof.
  move => x y a.
  move: a x y.
  elim => [x y b a' b' | a IH x y b a' b'].
    rewrite /d mul0n add0n.
    move => [-> Hr] [Hl' Hr'].
    case: a' Hl'.
      by rewrite mul0n add0n.
    move => a'' Hcontr.
    exfalso; have: b > y.
      move: Hcontr.
      rewrite mulSn -addnA.
      apply tst.
    move => Hl.
    move: (leq_gtF Hr).
    by rewrite Hl.
  case a' => [|a''].
    move => [Hl Hr] [Hl' Hr'].
    exfalso.
    move: Hl'; rewrite Hl mul0n add0n => H.
    move: Hr'.
    rewrite -H mulSn 2!addSn -addnA.
    rewrite -{3}(addn0 y).
    by rewrite ltn_add2l.  
  move => [Hl Hr] [Hl' Hr'].
  move: (Hl) (Hl') => ->.
  rewrite 2!mulSn 2!mulnS -addnA. 
  rewrite -[y.+1 + (a'' + a'' * y) + b']addnA.
  move /eqP.
  rewrite (eqn_add2l y.+1) => H.
  have: d (a * y.+1 + b) y a b.
    by split.
  have: d (a'' * y.+1 + b') y a'' b'.
    by split.
  rewrite 2!mulnS.
  move/eqP :H => ->.
  move => D' D.
  move: (IH _ _ _ _ _ D D') => [HL HR].
  by rewrite HL HR.
Qed.

(* 16.3.3 *)
Lemma d4: forall x y, x <= y -> d x y 0 x.
Proof.
  move => x y Hl.
  split => //.
Qed.

Lemma d5: forall x y a b, x > y -> d (x - y.+1) y a b -> d x y a.+1 b.
Proof.
  move => x y a b L [Hl Hr].
  split => //.
  rewrite mulSn -addnA -Hl.
  rewrite subnKC => //.
Qed.

(* 16.3.4 *)
(* TODO *)

(* 16.3.5 *)
(* TODO *)

(* 16.3.6 *)
(* TODO *)

(* 16.3.7 *)
(* TODO *)

(* 16.3.8 *)
(* TODO *)

(* 16.3.9 *)
(* TODO *)
