From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.


Lemma andb_true_elim b c: b && c -> c = true.
Proof.
by case/andP.
Restart.
case: c.
- by case: b.
by case: b.
Restart.
case: c; first done.
by case: b.
Restart.
case: c; [done | by case: b].
Restart.
by do 2![done | apply: eqxx | case: b | case: c]. (* 2 - numm of attempts (optional) *)
Qed.

(* do - repetition tactical *)


Inductive evenP n : Prop :=
  | Even0 of n = 0
  | EvenSS m of n = m.+2 & evenP m.

Fixpoint evenb n := if n is n'.+2 then evenb n' else n == 0.


Lemma evenP_contra n : evenP (n + 1 + n) -> False.
Proof.
elim: n=>//[| n Hn]; first by rewrite addn0 add0n; case=>//.
rewrite addn1 addnS addnC !addnS.
rewrite addnC addn1 addnS in Hn.
case=>// m /eqP.
by rewrite !eqSS; move/eqP=><-.
Qed.

Lemma evenb_contra n: evenb (n + 1 + n) -> False.
Proof.
elim: n=>[|n IH] //.
by rewrite addSn addnS.
Qed.

Lemma evenP_plus n m : evenP n -> evenP m -> evenP (n + m).
Proof.
elim=>//n'; first by move=>->; rewrite add0n.
move=> m' -> {n'} H1 H2 H3; rewrite addnC !addnS addnC.
apply: (EvenSS )=>//.
by apply: H2.
Qed.

Lemma evenb_plus n m : evenb n -> evenb m -> evenb (n + m).
Proof.
move: (leqnn n).
elim: n {-2}n.
- by case => //.
move => n Hn.
case=>//.
case=>// n0.
by move/ltnW /Hn=>//.
Qed.

Lemma nat2_ind (P: nat -> Prop):
  P 0 -> 
  P 1 -> 
  (forall n, P n -> P (n.+2)) -> 
  forall n, P n.
Proof.
move => H0 H1 H n.
suff: (P n /\ P (n.+1)) 
  by case.
by elim: n=>//n; case=> H2 H3; split=>//; last by apply: H.
Qed.

Lemma evenb_plus' n m : evenb n -> evenb m -> evenb (n + m).
Proof.
by elim/nat2_ind : n.
Qed.

Inductive beautiful (n: nat) : Prop :=
| b_0 of n = 0
| b_3 of n = 3
| b_5 of n = 5
| b_sum n' m' of beautiful n' & beautiful m' & n = n' + m'.

Search _.*2.
Search mul0n.
Search (_.+1 * _).

Theorem b_times2 n: beautiful n -> beautiful (2 * n).
Proof.
by move => H; rewrite mulnC muln2 -addnn; apply (b_sum _ n n) => //.
Qed.

Lemma b_timesm n m: beautiful n -> beautiful (m * n).
Proof.
elim m.
  move => H //; by apply b_0.
move => m' IHm' bn.
rewrite mulSn.
apply (b_sum _ n (m' * n)) => //.
by apply IHm'.
Qed.
