Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.


Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state), aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state), beval st b1 = beval st b2.



Theorem aequiv_example: aequiv <{ X - X }> <{ 0 }>.
Proof. 
  unfold aequiv. simpl. intro st. 
  Search (?n - ?n = 0).
  rewrite (sub_diag (st X)). reflexivity. Qed.

Theorem bequiv_example: bequiv <{ X - X = 0 }> <{ true }>.
Proof.
  unfold bequiv. simpl. intro st.
  rewrite (sub_diag (st X)). reflexivity. Qed.



Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state), (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').


Theorem skip_left : forall c,
  cequiv <{ skip; c }> c.
Proof.
  intro c. unfold cequiv. intros st st'. split.
  - intro H. inversion H. inversion H2. subst. apply H5.
  - intro H. apply (E_Seq CSkip c st st st' (E_Skip st) H).
Qed.

Theorem skip_right : forall c,
  cequiv <{ c ; skip }> c.
Proof.
  intro c. unfold cequiv. intros st st'. split.
  - intro H. inversion H. inversion H5. subst. apply H2.
  - intro H. apply (E_Seq c CSkip st st' st' H (E_Skip st')).
Qed.


Theorem if_true_simple : forall c1 c2,
  cequiv <{ if true then c1 else c2 end }> c1.
Proof.
  intros c1 c2. unfold cequiv. intros st st'. split.
  - intros H. 
    inversion H.
    + (* if true *)
      assumption.
    + (* if false *)
      simpl in H5. discriminate H5.
  - intros H.
    apply (E_IfTrue st st' _ c1 c2). { reflexivity. }
    assumption.
Qed.

Theorem if_true: forall b c1 c2,
  bequiv b <{true}> -> cequiv <{ if b then c1 else c2 end }> c1.
Proof.
  intros b c1 c2 Hb. unfold cequiv. intros st st'. split.
  - intros H. 
    inversion H.
    + (* if true *)
      assumption.
    + (* if false *)
      rewrite Hb in H5. discriminate H5.
  - intros H.
    apply (E_IfTrue st st' _ c1 c2). { rewrite -> Hb. reflexivity. }
    assumption.
Qed.

Theorem if_false : forall b c1 c2,
  bequiv b <{false}> -> cequiv <{ if b then c1 else c2 end }> c2.
Proof.
  intros b c1 c2 Hb. unfold cequiv. intros st st'. split.
  - intros H. 
    inversion H.
    + (* if true *)
      rewrite Hb in H5. discriminate H5.
    + (* if false *)
      assumption.
  - intros H.
    apply (E_IfFalse st st' _ c1 c2). { rewrite -> Hb. reflexivity. }
    assumption.
Qed.

Theorem swap_if_branches : forall b c1 c2,
  cequiv <{ if b then c1 else c2 end }> <{ if ~b then c2 else c1 end }>.
Proof.
  intros b c1 c2. unfold cequiv. intros st st'. split.
  - intros H. 
    inversion H.
    + (* if true *)
      apply (E_IfFalse st st' _ c2 c1). { simpl. rewrite H5. reflexivity. }
      assumption.
    + (* if false *)
      apply (E_IfTrue  st st' _ c2 c1). { simpl. rewrite H5. reflexivity. }
      assumption.
  - intros H.
    inversion H.
    + (* if true *)
      Search (negb ?b = true).
      apply (E_IfFalse st st' _ c1 c2). { simpl in H5. rewrite negb_true_iff  in H5. apply H5. }
      assumption.
    + (* if false *)
      apply (E_IfTrue  st st' _ c1 c2). { simpl in H5. rewrite negb_false_iff in H5. apply H5. }
      assumption.
Qed.


Theorem while_false : forall b c,
  bequiv b <{false}> -> cequiv <{ while b do c end }> <{ skip }>.
Proof.
  intros b c Hb. unfold cequiv. intros st st'. split.
  - intros H. inversion H.
    + (* while false *)
      apply E_Skip.
    + (* while true *)
      rewrite Hb in H2. discriminate H2.
  - intros H. inversion H.
    subst. apply (E_WhileFalse b st' c).
    rewrite Hb. reflexivity.
Qed.


Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> -> ~( st =[ while b do c end ]=> st' ).
Proof.
  intros b c st st' H Hcontr.
  remember <{ while b do c end }> as k eqn:Ek.
  induction Hcontr; try (discriminate Ek).
  - (* while false *)
    injection Ek as Ek1 Ek2. subst. rewrite H in H0. discriminate H0.
  - (* while true *)
    injection Ek as Ek1 Ek2. subst. apply IHHcontr2. reflexivity.
Qed.


Theorem while_true : forall b c,
  bequiv b <{true}> ->
  cequiv <{ while b do c end }> <{ while true do skip end }>.
Proof.
  intros b c Hb. split.
  - intros H. exfalso.
    apply (while_true_nonterm b c st st' Hb H).
  - intros H. exfalso.
    remember <{ true }> as k eqn:Ek.
    rewrite Ek in Hb.
    assert (G: bequiv k <{ true }>). { rewrite Ek. simpl. unfold bequiv. simpl. intro. reflexivity. }
    apply (while_true_nonterm k _ st st' G H).
Qed.

Theorem loop_unrolling : forall b c,
  cequiv <{ while b do c end }> <{ if b then c ; while b do c end else skip end }>.
Proof.
  intros b c. unfold cequiv. intros st st'. split.
  - intro H. inversion H.
    + (* E_WhileFalse *)
      apply (E_IfFalse st' st' b _ _).
      * assumption.
      * constructor.
    + (* E_WhileTrue *)
      apply (E_IfTrue st st' b _ _).  
      * assumption.
      * apply (E_Seq c _ st st'0 st' H3 H6).
  - intro H.
    destruct (beval st b) eqn:Eb.
    + (* b = true *)
      inversion H.
      * (* if true *)
        inversion H6. subst.
        apply (E_WhileTrue st st'1 st' b c Eb H9 H12).
      * (* if false *)
        rewrite H5 in Eb. discriminate Eb.
    + (* b = false *)
      inversion H.
      * (* if true *) rewrite H5 in Eb. discriminate Eb.
      * (* if false *) 
        subst.
        inversion H6. subst.
        apply (E_WhileFalse b st' c Eb).
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
  intros c1 c2 c3. unfold cequiv. intros st st'. split.
  - intro H.
    inversion H.
    inversion H2. subst.
    apply (E_Seq c1 <{ c2;c3 }> st st'1 st' H8).
    apply (E_Seq c2 c3 st'1 st'0 st' H11 H5).
  - intro H.
    inversion H.
    inversion H5. subst.
    assert (G: st =[ c1; c2 ]=> st'1). {
      apply (E_Seq c1 c2 st _ st'1 H2 H8).
    }
    apply (E_Seq <{ c1;c2 }> c3 st st'1 st' G H11).
Qed.

Theorem identity_assignment : forall x,
  cequiv <{ x := x }> <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

Theorem assign_aequiv : forall (x : string) a,
  aequiv x a -> cequiv <{ skip }> <{ x := a }>.
Proof.
  intros x a Ha. 
  split; intro H.
  - inversion H. subst.
    Check t_update_same.
    assert (G: (x !-> aeval st' a ; st') = st'). {
      rewrite <- Ha.
      apply t_update_same.
    }
    assert (G': (st' =[ x := a ]=> st') = (st' =[ x := a ]=> (x !-> aeval st' a ; st'))). {
      rewrite G.
      reflexivity.
    }
    rewrite G'.
    apply (E_Asgn st' _ _ x).
    reflexivity.
  - inversion H. subst.
    assert (G: (x !-> aeval st a ; st) = st). {
      rewrite <- Ha.
      apply t_update_same.
    }
    rewrite G.
    constructor.
Qed.

