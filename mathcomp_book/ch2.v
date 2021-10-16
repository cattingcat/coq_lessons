From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "=".

About eq.

Fail Check 2 = [:: 3].


Lemma first_trivial: 3 = 3.
Proof. by []. Qed.

About first_trivial.

Search "~~".

Lemma negbK (b: bool) : ~~ (~~ b) = b.
Proof.
  case: b.
    by [].
    by [].
Qed.

Lemma negbK' (b: bool) : ~~ (~~ b) = b.
Proof. by case: b. Qed.

Check negbK.


Lemma leqn0 n: (n <= 0) = (n == 0).
Proof.
  case: n => [| k]. by []. by []. Qed.

Lemma leqn0' n: (n <= 0) = (n == 0).
Proof. by case: n => [| k]. Qed.

Lemma muln_eq0 m n :
  (m * n == 0) = (m == 0) || (n == 0).
Proof.
  case: m => [|m] //. (* // - try to solve easy case automatically*)
  case: n => [|n]; last first. (* last first - swap branches *)
    by [].
  (* rewrite muln0 //. *)
  by rewrite muln0.
Qed.

Lemma leqE m n : (m <= n) = (m - n == 0).
Proof. by []. Qed.

Lemma leq_mul121 m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
  (* by rewrite !leqE -mulnBr muln_eq0. *)
  rewrite !leqE. (* ! - rewrite all *)
  rewrite -mulnBr. (* -  - rewrite backward *)
  rewrite muln_eq0.
  by [].
Qed.


Definition commut {S T: Type} (op: S -> S -> T):= forall (a b: S), op a b = op b a.
About commut.


Section tst.
Variables a b : nat.
Hypothesis ab_neq : ~~ (a == b).

Lemma tst_lemma: forall c, c - a == b.
Proof. Admitted.

End tst.
Check tst_lemma.



Lemma lenn n: n <= n. Proof. by []. Qed.
Lemma examplelenn a b: a + b <= a + b.
Proof. apply: lenn. Qed.

Hint Resolve lenn: local.
Lemma examplelenn1 a b: a + b <= a + b.
Proof. by []. Qed.


Lemma ex m p : prime p -> p %| m`! + 1 -> m < p.
Proof.
  move=> prime_p.
  apply: contraLR.
  rewrite -leqNgt.
  move=> leq_p_m.
  rewrite dvdn_addr.
    rewrite gtnNdvd.
      by [].
      by [].
      by apply: prime_gt1.
  apply: dvdn_fact.
    rewrite prime_gt0.
      by [].
  apply: prime_p.
Qed.

Lemma ex2 m p : prime p -> p %| m`! + 1 -> m < p.
Proof.
  move=> prime_p; apply: contraLR; rewrite -leqNgt; move=> leq_p_m.
  rewrite dvdn_addr.
    by rewrite gtnNdvd // prime_gt1.
  by rewrite dvdn_fact // prime_gt0.
Qed.

Lemma addn0 m: m + 0 = m.
Proof.
  elim: m => [ // | m IHm ].
  rewrite addSn IHm //.
Qed.

About last_ind.
Print rcons.

Lemma foldl_rev T A f (z: A) (s: seq T): 
  foldl f z (rev s) = foldr (fun x s => f s x) z s.
Proof.
  elim/last_ind: s z => [| s x IHs] z //. (* generalize z *)
  by rewrite -cats1 foldr_cat -IHs cats1 rev_rcons.
Qed.













