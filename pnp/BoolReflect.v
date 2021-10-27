From mathcomp
Require Import ssreflect ssrfun eqtype ssrnat ssrbool prime.

From QuickChick Require Import QuickChick.

Module BoolReflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "_ = _".
Print eq.


Section Tst1.
Variables S T: bool -> Prop.
Hypothesis STequiv : forall a b, T a <-> S (a || b).

Lemma ST_False a b: (T a -> False) -> S (a || b) -> False.
Proof.
by move => H /STequiv. (* views for ctx *)
Qed.

Definition TS_neg: forall a, T (negb a) -> S ((negb a) || a).
Proof.
move => a H.
apply/STequiv. (* views for goal *)
done.
Qed.

End Tst1.


Definition prime_spec n m : Prop := m = (if prime n then 1 else 2).
Definition discr_prime n := (if prime n then 0 else 1) + 1.
Lemma discr_prime_spec : forall n, prime_spec n (discr_prime n).
Proof.
move => n.
rewrite /prime_spec /discr_prime.
by case (prime n).
Qed.


Section Tst2.
Variables do_check1 do_check2 : nat -> bool.

Hypothesis H: forall n, do_check2 n -> prime n.

Lemma check_prime n : (do_check1 n) && (do_check2 n) -> prime n.
Proof.
case andP => //.
move => [_ dc2] _.
apply (H _ dc2).
Qed.
End Tst2.



Lemma trueP : reflect True true.
Proof. by constructor. Qed.

Lemma falseP : reflect False false.
Proof. by constructor. Qed.

Goal false -> False.
Proof. move=> f. by case:falseP. Qed.


Definition andb_orb b1 b2: b1 && b2 -> b1 || b2.
Proof.
case/andP => H1 H2.
by apply/orP; left.
Qed.


Definition XOR (P Q: Prop) := (P \/ Q) /\ ~(P /\ Q).

Definition xorb b := if b then negb else fun x => x.

Lemma xor_gen (b1 b2 : bool)(P1 P2: Prop):
  reflect P1 b1 ->
  reflect P2 b2 ->
  reflect (XOR P1 P2) (xorb b1 b2).
Proof.
case => p1; case => p2; rewrite /XOR; constructor.
- case => _ H. by apply H.
- split.
    by left.
  case => _ p2'. by apply p2.
- split.
    by right.
  case => p1' _. by apply p1.
- case => Hp12 nhp12.
  by case Hp12.
Qed.


Lemma xorP (b1 b2 : bool): reflect (XOR b1 b2) (xorb b1 b2).
Proof.
by apply xor_gen; [case b1 | case b2]; constructor.
Qed.


Definition XOR' (P Q: Prop) := (P /\ ~Q) \/ (~P /\ Q).

Search (~(?P /\ ?Q)).

Lemma XORequiv P Q: XOR P Q <-> XOR' P Q.
Proof.
rewrite /XOR /XOR'.
split.
  move => [[p | q] nh].
    left. split. apply p.
      move => q. by apply nh.
    right. split. move => p. by apply nh.
      apply q.
  move => [[p nq] | [np q]].
    split. by left.
      move => [_ q]. by apply nq.
    split. by right.
      move => [p _]. by apply np.
Qed.

Lemma xorP' (b1 b2 : bool): reflect (XOR' b1 b2) (xorb b1 b2).
Proof.
case: xorP => /XORequiv; by constructor.
Qed.

Lemma xorbC (b1 b2: bool) : (xorb b1 b2) = (xorb b2 b1).
Proof. by case: b1; case: b2. Qed.

Lemma xorbA (b1 b2 b3: bool) : (xorb (xorb b1 b2) b3) = (xorb b1 (xorb b2 b3)).
Proof. by case: b1; case: b2; case: b3=>//. Qed.


Lemma xorCb (b1 b2: bool) : (XOR b1 b2) <-> (XOR b2 b1).
Proof.
by split; move /xorP; rewrite xorbC; apply/xorP.
Qed.

Lemma xorAb (b1 b2 b3: bool) : (XOR (XOR b1 b2) b3) <-> (XOR b1 (XOR b2 b3)).
Proof.
split.
  move => H.
  apply/(xor_gen b1 (xorb b2 b3)).
    by case b1; constructor.
    by apply xorP.
    rewrite -xorbA.
      apply/(xor_gen _ _ (XOR b1 b2) b3).
        by apply xorP.
        by case b3; constructor.
        done.
  move /(xor_gen b1 (xorb b2 b3)).
  move => H.
  apply/(xor_gen (xorb b1 b2) b3).
    by apply xorP.
    by case b3; constructor.
    rewrite xorbA; apply: H.
      by case b1; constructor.
      by apply xorP.
Qed.


Definition foo (x y: nat) := if x == y then 1 else 0.

Goal forall x y, x = y -> foo x y = 1.
Proof.
move => x y; rewrite /foo.
by move/eqP => ->. (* move applies to top stack *)
Qed.


Lemma ExistsUnique1 A (P : A -> A -> Prop):
  (exists !x, exists y, P x y) ->
  (exists !x, exists y, P y x) ->
  (exists !x, exists !y, P x y).
Proof.
move => [x [[y' pxy'] uni_x]] [y [[x' px'y] uni_y]].
have Ex: x = x'.
  apply: uni_x.
  by exists y.
have Ey: y = y'.
  apply: uni_y.
  by exists x.
exists x.
split.
  exists y.
  split.
  * by rewrite Ex.
  * move => k pk.
    apply: uni_y.
    by exists x.
  * move => k [y'' [h u]].
    apply: uni_x.
    by exists y''.
Qed.

Definition Q x y : Prop :=
  (x == true) && (y == true) || (x == false).

Lemma qlm : (exists !x, exists !y, Q x y).
Proof.
exists true.
split.
exists true.
split.
  done.
  case => //.
  case => //.
  move => [y [u h]].
  have yt: y = true.
    by apply h.
  have yf: y = false.
    by apply h.
by move: yt yf => ->.
Qed.

Lemma ExistsUnique2: (forall A (P : A -> A -> Prop),
  (exists !x, exists !y, P x y) ->
  (exists !x, exists y, P x y) /\ (exists !x, exists y, P y x)) ->
  False.
Proof.
move => H.
have t: (exists ! x, exists y, Q x y) /\ (exists ! x, exists y, Q y x).
  apply: (H _ Q qlm).
case: t => Hcontrl Hcontrr.
case: Hcontrl => x [[x' p] u].
case: x u p => u p.
  have contra: true = false.
    apply u.
    by exists true.
  by move: contra.
have contra: false = true.
  apply u.
  by exists true.
by move: contra.
Qed.
