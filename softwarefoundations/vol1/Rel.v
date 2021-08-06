Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Module Rel.
Import IndProp.


Definition relation (X: Type) := X -> X -> Prop.

Print le.

Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat (n: nat): nat -> Prop :=
  | nn: next_nat n (S n).

Print next_nat.

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros.
  destruct H.
  destruct H0.
  reflexivity.
Qed.

Print le.

Theorem le_not_a_partial_function :
  ~(partial_function le).
Proof.
  unfold not, partial_function.
  intros.
  discriminate (H 0 1 2).
  - apply le_S. apply le_n.
  - apply le_S. apply le_S. apply le_n.
Qed.

Theorem total_relation_not_a_partial_function :
  ~(partial_function total_relation).
Proof.
  unfold not, partial_function.
  intros.
  discriminate (H 0 1 2).
  - apply total.
  - apply total.
Qed.


Definition reflexive {X: Type} (R: relation X) :=
  forall (a : X), R a a.

Theorem le_reflexive : reflexive le.
Proof.
  unfold reflexive.
  apply le_n.
Qed.



Definition transitive {X: Type} (R: relation X) :=
  forall (a b c : X), (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  unfold transitive.
  intros.
  induction H0 as [| n IH].
  - apply H.
  - apply le_S. apply IHIH.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold transitive, lt.
  intros.
  induction H0 as [| n IH IH1].
  - apply le_S. apply H.
  - apply le_S. apply IH1.
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S. apply Hnm.
  - apply le_S. apply IHHm'o.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o' IH].
  - exfalso. inversion Hmo.
  - remember (S m) as sm.
    remember (S o') as so'.
    destruct Hmo as [| k' H].
    + rewrite -> Heqso' in Heqsm.
      injection Heqsm as Heqsm.
      rewrite <- Heqsm in Hnm.
      rewrite -> Heqso'. apply le_S.
      apply Hnm.
    + apply le_S. 
      injection Heqso' as Heqso'.
      rewrite -> Heqso'.
      apply IH.
      rewrite <- Heqso'.
      apply H.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros.
  assert (G: n <= S n). { apply le_S. apply le_n. }
  apply (le_trans n (S n) m G H).
Qed.


Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros.
  assert (G: m <= S m). { apply le_S. apply le_n. }
  remember (S n) as sn eqn:Esn.
  remember (S m) as sm eqn:Esm.
  destruct H as [| m' H].
  - rewrite -> Esm in Esn. injection Esn as Esn. rewrite -> Esn.
    apply le_n.
  - apply le_Sn_le.
    rewrite <- Esn.
    injection Esm as Esm.
    rewrite <- Esm.
    apply H.
Qed.

Theorem no_less_self: forall n, ~(S n <= n).
Proof.
  unfold not. intros.
  induction n as [| n' IH].
  - inversion H.
  - apply le_S_n in H.
    apply (IH H).
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall (a b : X), (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~(symmetric le).
Proof.
  unfold not, symmetric.
  intros.
  apply (no_less_self 0).
  apply (H 0 1).
  apply le_S.
  apply le_n.
Qed.



Definition antisymmetric {X: Type} (R: relation X) :=
  forall (a b : X), (R a b) -> (R b a) -> a = b.


Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b Hab Hba.
  destruct Hab as [| b' H].
  - reflexivity.
  - exfalso.
    apply (no_less_self b').
    apply (le_trans (S b') a b' Hba H).
Qed.


Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  unfold lt.
  intros.
  apply le_S_n.
  apply (le_trans (S n) m (S p) H H0).
Qed.




Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  split.
  - apply le_reflexive.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.





Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

End Rel.
