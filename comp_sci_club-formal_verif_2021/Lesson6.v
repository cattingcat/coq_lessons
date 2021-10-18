From mathcomp Require Import all_ssreflect.

Module Lesson6.

Lemma addC : commutative addn.
Proof.
elim => [| x' IHx] y.
  by rewrite addn0.
Search (_ + _.+1).
by rewrite addSn IHx addnS.
Qed.

Lemma addC2 : commutative addn.
Proof.
elim => [| x' IHx] y; first by rewrite addn0.
by rewrite addSn IHx addnS.
Qed.

Locate "`!".
Print factorial.
Print nosimpl.
Print fact_rec.

(* /=  - simpl *)

Fixpoint factorial_helper n acc :=
  if n is n'.+1 then factorial_helper n' (n * acc) else acc.

Definition my_factorial n := factorial_helper n 1.

Compute (my_factorial 5).

Lemma my_factorial_correct: forall n, my_factorial n = n`!.
Proof.
elim => [|n' IHn] //.
rewrite /my_factorial /factorial /= muln1.
rewrite /my_factorial /factorial in IHn.
rewrite -{}IHn.       (* {}  - remove hypotesis from context *)
rewrite /factorial_helper /=.
case: n'; first by done.
Abort.

Lemma factorial_helper_correct:
  forall n a, factorial_helper n a = n`! * a.
Proof.
elim => [| n' IHn] a /=.
  by rewrite /factorial /= mul1n.
rewrite {}IHn.
by rewrite factS mulnCA mulnA.
Qed.

Lemma my_factorial_correct: forall n, my_factorial n = n`!.
Proof.
rewrite /my_factorial => n.
by rewrite factorial_helper_correct muln1.
Qed.

Search (_ * 1).
Search left_id muln.
Search right_id muln.


Fixpoint fib (n: nat) :=
  if n is (n''.+1 as n').+1 
    then fib n'' + fib n'
    else n.

Lemma tst1 n: fib n.+2 = 0.
Proof. move=> /=. Abort.

Arguments fib n : simpl nomatch. (* don't simpl unti matches *)

Lemma tst1 n: fib n.+2 = 0.
Proof. move=> /=. Abort.


Fixpoint fib_iter n f0 f1 :=
  if n is n'.+1 then fib_iter n' f1 (f0 + f1) else f0.
Arguments fib_iter n : simpl nomatch.

Lemma fib_iterS n f0 f1: fib_iter (n.+1) f0 f1 = fib_iter n f1 (f0 + f1).
Proof. done. Qed.

Lemma fib_iter_sum n f0 f1:
  fib_iter n.+2 f0 f1 = fib_iter n f0 f1 + fib_iter n.+1 f0 f1.
Proof.
elim: n f0 f1 => [//| n' IHn] f0 f1. (* :  - generalize n f0 f1 and then elim top (n) *)
(* : n f0 f1 = gen f1, gen f0, gen n *)
rewrite fib_iterS {}IHn.
done.
Qed.


Lemma fib_iter_correct n:
  fib_iter n 0 1 = fib n.
Proof.
elim: n => [//|n' IHn].
rewrite fib_iterS.
Abort.

Lemma nat_ind2 (P: nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+1 -> P n.+2) ->
  (forall n, P n).
Proof.
move=> p0 p1 pstep n.
have: P n /\ P n.+1; last by case.
elim: n => [//| n' [IHn' IHSn']].
split=> //.
apply (pstep n' IHn' IHSn').
Qed.

Lemma nat_ind2' (P: nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+1 -> P n.+2) ->
  (forall n, P n).
Proof.
move=> p0 p1 pstep n.
suff: P n /\ P n.+1 by case. (* like have but swaps goals *)
elim: n => [//| n' [IHn' IHSn']].
split=> //.
apply (pstep n' IHn' IHSn').
Qed.


Lemma nat_ind3' (P: nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+1 -> P n.+2) ->
  (forall n, P n).
Proof.
move=> p0 p1 pstep n.
suff: P n /\ P n.+1 by case. (* like have but swaps goals *)
elim: n => // n.
case.
move /pstep. (* Apply something to head *)
move => p12.
move /[dup].
move /p12.
done.
Qed.

Lemma fib_iter_correct n:
  fib_iter n 0 1 = fib n.
Proof.
(*elim/nat_ind2: n => [//|//| n' IHn1 IHn2].*)
elim/nat_ind2: n => // n' IHn1 IHn2.
rewrite fib_iter_sum {}IHn1 {}IHn2.
done.
Qed.

About ltn_ind.

Lemma fib_iter_correct' n:
  fib_iter n 0 1 = fib n.
Proof.
elim/ltn_ind: n => n IHn.
Fail case: n. (* IHn depends on n *)
case: n IHn => // n IHn.
case: n IHn => // n IHn.
rewrite fib_iter_sum.
(*case n' => // n.*)
rewrite !IHn. (* ! - repeat *)
- done.
- done.
done.
Restart.
elim/ltn_ind: n => [] // [] // [] // n IHn.
by rewrite fib_iter_sum !IHn.
Qed.

(* {1}<-  - rewrite first entry backwards *)

End Lesson6.
