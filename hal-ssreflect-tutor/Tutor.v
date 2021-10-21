From Coq Require Import Program.
From QuickChick Require Import QuickChick.
From mathcomp Require Import all_ssreflect.
Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section HilbertSaxiom.
Variables A B C : Prop.
Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> hAiBiC hAiB hA.
move: hAiBiC.
(* move: name - removes from ctx, moves to stack *)
(* move: (name) - moves to stack without remove from ctx *)
apply.
by [].
by apply: hAiB.
Qed.

Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).
Lemma HilbertS2 : C.
Proof.
apply: hAiBiC; first by apply: hA.
exact: hAiB.
Qed.

Lemma HilbertS3 : C.
Proof. by apply: hAiBiC; last exact: hAiB. Qed.

Lemma HilbertS4 : C.
Proof. exact: (hAiBiC _ (hAiB _)). Qed.

Lemma HilbertS5 : C.
Proof. exact: hAiBiC (hAiB _). Qed.

Lemma HilbertS6 : C.
Proof. exact: HilbertS5. Qed.

Print HilbertS5.
Print HilbertS2.
Print HilbertS.
Check HilbertS.

End HilbertSaxiom.


Print bool.

Section Symmetric_Conjunction_Disjunction.
Lemma andb_sym : forall A B : bool, A && B -> B && A.
Proof.
case.
by case.
by [].
Qed.

Lemma andb_sym2 : forall A B : bool, A && B -> B && A.
Proof. by case; case. Qed.

Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
Proof. by do 2! case. Qed. (* do 2! - repeat next tactic two times *)

Variables (C D : Prop) (hC : C) (hD : D).

Check (and C D).

Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A.
Proof. by move=> A1 B []. Qed. (* [] - case *)

Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
Proof. by move=> A B [hA | hB]; [apply: or_intror | apply: or_introl]. Qed.

Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
Proof. by move=> [] [] AorB; apply/orP; move/orP : AorB. Qed.

(* apply/orP - rephrase goal *)
(* move/orP  - rephrase stack top *)

End Symmetric_Conjunction_Disjunction.


Print ex.

Section R_sym_trans.
Variables (D : Type) (R : D -> D -> Prop).
Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
Proof.
move=> x [y Rxy].
by apply (R_trans Rxy (R_sym Rxy)).
Qed.
End R_sym_trans.


Section Smullyan_drinker.
Variables (D : Type)(P : D -> Prop).
Hypothesis (d : D) (EM : forall A, A \/ ~A).

Lemma drinker : exists x, P x -> forall y, P y.
Proof.
case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy]; first by exists y.
exists d => _ y; case: (EM (P y)) => // notPy.
by case: nonotPy; exists y.
Qed.
End Smullyan_drinker.


Section Equality.
Variable f : nat -> nat.

Hypothesis f00 : f 0 = 0.
Lemma fkk : forall k, k = 0 -> f k = k.
Proof.
move=> k k0.
by rewrite k0.
Qed.

Lemma fkk2 : forall k, k = 0 -> f k = k.
Proof. by move=> k ->. Qed.

Variable f10 : f 1 = f 0.

Lemma ff10 : f (f 1) = 0.
Proof. by rewrite f10 f00. Qed.

Variables (D : eqType) (x y : D).

Lemma eq_prop_bool : x = y -> x == y.
Proof. by move/eqP. Qed.

Lemma eq_bool_prop : x == y -> x = y.
Proof. by move/eqP. Qed.

End Equality.


Section Using_Definition.
Variable U : Type.
Definition set := U -> Prop.
Definition subset (A B : set) := forall x, A x -> B x.
Definition transitive (T : Type) (R : T -> T -> Prop) :=
  forall x y z, R x y -> R y z -> R x z.

Lemma subset_trans : @transitive set subset.
Proof.
rewrite /transitive /subset => x y z subxy subyz t xt.
by apply: subyz; apply: subxy.
Qed.

Lemma subset_trans2 : @transitive set subset.
Proof.
move=> x y z subxy subyz t.
move/subxy. by move/subyz. (* move/name - apply name to top stack *)
Qed.
End Using_Definition.


Lemma three : S (S (S O)) = 3 /\ 2 = 0.+1.+1.
Proof. by []. Qed.


Print le. (* vanilla le *)

Lemma concrete_le : le 1 3.
Proof. by apply: (Le.le_trans _ 2); apply: Le.le_n_Sn. Qed.

Lemma concrete_big_le : le 16 64.
Proof. by auto 47 with arith. Qed.

Lemma plus_commute : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
elim=> [| n IHn m].
- elim => [//| n IHn].
    by rewrite -[0 + n.+1]/(0 + n).+1 IHn.
rewrite -[n.+1 + m]/(n + m).+1 IHn. elim: m => [//| m IHm ].
  by rewrite -[m.+1 + n]/(m + n).+1 IHm.
Qed.


Definition edivn_rec d := fix loop (m q : nat) {struct m} :=
if m - d is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn m d := if d > 0 then edivn_rec d.-1 m 0 else (0, m).


CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
  | EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) : edivn_spec m d (q, r).

(* CoInductive doesn't generate induction principles *)

CoInductive edivn_spec2 (m d : nat) : nat * nat -> Type :=
  | EdivnSpec2 : forall q r, m = q * d + r -> (d > 0 -> r < d) -> edivn_spec2 m d (q, r).

CoInductive edivn_spec3 (m d : nat) : nat * nat -> Type :=
  | EdivnSpec3 q r (H1: m = q * d + r) (H2: d > 0 -> r < d) : edivn_spec3 m d (q, r).

About mulSnr.
Search (?a.+1 + ?b = ?a + ?b.+1).
Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
rewrite /edivn => m [|d] //=. rewrite -{1}[m]/(0 * d.+1 + m). (* {1} - rewrite first entry *)
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
rewrite subn_if_gt; case: ltnP => [// | le_dm].
rewrite -{1}(subnK le_dm) -addSn. rewrite addSnnS (addnC (m - d) d.+1) addnA -mulSnr. apply: IHn.
apply: leq_trans le_mn; exact: leq_subr.
Qed.


Lemma edivn_eq : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
case: edivnP lt_rd => q' r'; rewrite d_pos /=.
wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.







