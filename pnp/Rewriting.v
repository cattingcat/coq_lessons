From mathcomp
Require Import ssreflect ssrfun eqtype ssrnat ssrbool.

From QuickChick Require Import QuickChick.

Module Rewriting.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "_ = _".
Print eq.


Inductive my_eq {A : Type} (x : A) : A -> Prop :=  my_eq_refl : my_eq x x.
Notation "a === b" := (my_eq a b) (at level 70).

Definition my_eq_sym: forall A (x y: A), x === y -> y === x 
:=
  fun A x y (r: x === y) =>
    match r 
      in (_ === x')
      return (x' === x)
    with
    | my_eq_refl _ => my_eq_refl _
    end.

Lemma my_eq_sym' A (x y: A): x === y -> y === x.
Proof.
case.
constructor.
Qed.

Definition disaster: 1 === 2 -> False
:=
  fun contra => 
    match contra 
      in (_ === x')
      return (if x' is 2 then False else True)
    with 
    | my_eq_refl _ => I
    end.

Lemma disaster': 2 === 1 -> False.
Proof.
case. (* doesn't work *)
Restart.
move => H.
pose D x := if x is 2 then False else True.
have D1: D 1.
  by [].
case: H D1.
rewrite /D.
done.
Qed.

Lemma disaster'2: 1 === 2 -> False.
Proof.
case. (* doesn't work *)
Restart.
pose D x := if x is 1 then False else True.
have D2: D 2.
  by constructor.
move => H.
move: H D2.
case. (* rewrites D1 to D 1 in goal  *)
rewrite /D.
done.
Qed.


Definition f x y := x + y.

Goal forall x y, x + y + (y + x) = f y x + f y x.
Proof.
move => x y.
rewrite /f.
congr (_ + _).
rewrite [y + _]addnC.
done.
Qed.

Goal forall x y z, (x + (y + z)) = (z + y + x).
Proof.
move => x y z.
rewrite [x + (_ + _)]addnC.
rewrite [y + z]addnC.
done.
Qed.

Lemma addnCA: forall m n p, m + (n + p) = n + (m + p).
Proof.
elim=> [|m IHm] n p.
  by rewrite !add0n.
rewrite !addSnnS.
rewrite -addnS.
rewrite IHm.
done.
Qed.

Lemma addnC: forall m n, m + n = n + m.
Proof.
move=> m n.
rewrite -{1}[n]addn0. (* first entry of pattern *)
rewrite addnCA.
rewrite addn0.
done.
Qed.


Lemma huh n m: (m <= n) /\ (m > n) -> False.
Proof.
suff X: (m <= n) -> ~(m > n). (* suff lije have, but different goal order *)
  by case => /X.
elim: m n => [| m IHm] [|n] //.
exact: IHm.
Qed.

Definition maxn m n := if m < n then n else m.

Search (_ < _).

Lemma tst m n : maxn m.+1 n.+1 = (maxn m n).+1.
Proof.
rewrite /maxn //.
have H: (m.+1 < n.+1) = (m < n).
  done.
rewrite H.
by case: (m < n).
Qed.

Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.
Proof.
elim: m n => [|m IHm ] [|n] //.
rewrite tst.
by exact: IHm.
Qed.



Inductive leq_xor_gtn m n : bool -> bool -> Set :=
| LeqNotGtn of m <= n : leq_xor_gtn m n true false
| GtnNotLeq of n <  m : leq_xor_gtn m n false true.

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
rewrite ltnNge.
(* case with name *)
by case le_mn: (m <= n); constructor=>//; rewrite ltnNge le_mn.
Qed.



Lemma huh' n m: (m <= n) /\ (m > n) -> False.
Proof.
case: leqP.
  move=> _ [_ contra] //.
move=> _ [contra _] //.
Qed.

Search (_ < _ -> _ <= _).

Lemma max_is_max' m n: n <= maxn m n /\ m <= maxn m n.
Proof.
rewrite /maxn.
case: leqP => //.
move => H.
split.
  by apply: leqnn.
by apply: ltnW.
Qed.


Lemma max_l m n: n <= m -> maxn m n = m.
Proof.
move => H.
by rewrite /maxn ltnNge H.
Qed.

Lemma succ_max_distr n m : (maxn n m).+1 = maxn (n.+1) (m.+1).
Proof.
by rewrite tst.
Qed.

Lemma plus_max_distr_l m n p: maxn (p + n) (p + m) = p + maxn n m.
Proof.
elim: p => [| p IHp ] //.
by rewrite !addSn -succ_max_distr IHp.
Qed.

Inductive nat_rels m n : bool -> bool -> bool -> Set :=
| CompareNatLt of m < n : nat_rels m n true false false
| CompareNatGt of m > n : nat_rels m n false true false
| CompareNatEq of m == n : nat_rels m n false false true.

Search (_ < _ = _).
Search (?n <= ?m = _ || _).
Search (_ || _ = false -> _).
Search (~~(_ || _) = _).
Search ((_ && _ = _) -> _).
Search (?n < ?m -> ~~ ?n == _?m).
Search (~~ ?a == ?b = true -> _).
Search (_ && _ = true -> _).
Search (?a = false -> ~~ ?a).
Search ( _ && _ -> ?a == ?b).
Search (eq_op).
Search "symm".
About ltnNge.

About ltn_neqAle.
About eqn_leq.
About ltnP.

Lemma m_le_n_helper m n: m < n -> n < m = false /\ m == n = false.
Proof.
rewrite (ltnNge m n) leq_eqVlt negb_or.
move /andP => [neq nle].
split; apply negbTE.
  done.
rewrite eq_sym.
done.
Qed.

Lemma natrelP m n : nat_rels m n (m < n) (n < m) (m == n) .
Proof.
case m_le_n: (m < n).
  case (m_le_n_helper m n m_le_n) => [-> ->].
  by constructor.
case m_gt_n: (n < m).
  suff m_neq_n: (m == n = false).
  by rewrite (m_neq_n); constructor.
    case (m_le_n_helper n m m_gt_n) => [_ r].
    rewrite eq_sym.
    done.
suff mn_eq: (m == n).
  rewrite mn_eq.
  by constructor.
by rewrite eqn_leq [m<=n]leqNgt [n<=m]leqNgt m_le_n m_gt_n.
Qed.


Definition minn m n := if m < n then m else n.
Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Proof.
rewrite /minn /maxn.
case leqP => H.
  by rewrite addnC.
by rewrite addnC.
Qed.
