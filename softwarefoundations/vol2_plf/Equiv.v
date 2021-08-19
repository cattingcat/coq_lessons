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



Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof. intros a st. reflexivity. Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp), aequiv a1 a2 -> aequiv a2 a1.
Proof. intros a1 a2 H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp), aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof. unfold bequiv. intros b st. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp), bequiv b1 b2 -> bequiv b2 b1.
Proof. unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp), bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof. unfold cequiv. intros c st st'. reflexivity. Qed.

Lemma sym_cequiv : forall (c1 c2 : com), cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity. Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23. Qed.



Theorem CAsgn_congruence : forall x a a',
  aequiv a a' -> cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity. Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' -> st =[ while b' do c' end ]=> st').
  { unfold bequiv, cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  }
  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  unfold cequiv. intros c1 c1' c2 c2' Hec1 Hec2 st st'. 
  split; intro H.
  - inversion H. subst.
    rewrite Hec1 in H2.
    rewrite Hec2 in H5.
    apply (E_Seq c1' c2' st st'0 st' H2 H5).
  - inversion H. subst.
    rewrite <- Hec1 in H2.
    rewrite <- Hec2 in H5.
    apply (E_Seq c1 c2 st st'0 st' H2 H5). Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }> <{ if b' then c1' else c2' end }>.
Proof.
  unfold bequiv, cequiv. intros b b' c1 c1' c2 c2' Heb Hec1 Hec2 st st'. 
  split; intro H.
  - inversion H.
    + (* if true *)
      subst. 
      apply (E_IfTrue st st' b' c1' c2').
      * rewrite <- Heb. assumption.
      * rewrite <- Hec1. assumption.
    + (* if false *)
      subst. 
      apply (E_IfFalse st st' b' c1' c2').
      * rewrite <- Heb. assumption.
      * rewrite <- Hec2. assumption.
  - inversion H.
    + (* if true *)
      subst. 
      apply (E_IfTrue st st' b c1 c2).
      * rewrite Heb. assumption.
      * rewrite Hec1. assumption.
    + (* if false *)
      subst. 
      apply (E_IfFalse st st' b c1 c2).
      * rewrite Heb. assumption.
      * rewrite Hec2. assumption. Qed.



Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := 0
       else
         Y := 42
       end }>
    (* Program 2: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := X - X (* <--- Changed here *)
       else
         Y := 42
       end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAsgn_congruence. unfold aequiv. simpl.
      symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.




Definition atrans_sound (atrans : aexp -> aexp) : Prop := forall (a : aexp), aequiv a (atrans a).
Definition btrans_sound (btrans : bexp -> bexp) : Prop := forall (b : bexp), bequiv b (btrans b).
Definition ctrans_sound (ctrans : com -> com  ) : Prop := forall (c : com), cequiv c (ctrans c).


Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n  => ANum n
  | AId x   => AId x
  | <{ a1 + a2 }> =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }> =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 : fold_constants_aexp <{ (1 + 2) * X }> = <{ 3 * X }>.
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>  => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2')         => <{ a1' = a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2')         => <{ a1' <= a2' }>
      end
  | <{ ~b1 }> =>
      match (fold_constants_bexp b1) with
      | <{true}>  => <{false}>
      | <{false}> => <{true}>
      | b1'       =><{ ~b1' }>
      end
  | <{ b1 && b2 }> =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (<{true}>, <{true}>)    => <{true}>
      | (<{true}>, <{false}>)   => <{false}>
      | (<{false}>, <{true}>)   => <{false}>
      | (<{false}>, <{false}>)  => <{false}>
      | (b1', b2')              => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex2 : fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }> = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }>    => <{ skip }>
  | <{ x := a }>  => <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }> => <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b'        => <{ if b' then fold_constants_com c1 else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b'        => <{ while b' do (fold_constants_com c1) end }>
      end
  end.


Theorem fold_constants_aexp_sound : atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (<{ a1 + a2 }>)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

Theorem fold_constants_bexp_sound: btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    assert (G1: aequiv a1 a1'). { subst a1'. apply (fold_constants_aexp_sound a1). }
    replace (aeval st a1) with (aeval st a1') by (rewrite G1; reflexivity).
    assert (G2: aequiv a2 a2'). { subst a2'. apply (fold_constants_aexp_sound a2). }
    replace (aeval st a2) with (aeval st a2') by (rewrite G2; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (n <=? n0); reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound : ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
             apply fold_constants_aexp_sound.
  - (* ; *)  apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          fold_constants_bexp_sound.) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - (* while *)
    destruct (fold_constants_bexp b) eqn:Heqb.
    + (* while true  *)  apply while_true.  rewrite <- Heqb. apply fold_constants_bexp_sound.
    + (* while false *)  apply while_false. rewrite <- Heqb. apply fold_constants_bexp_sound.
    + (* while a = b *)  apply CWhile_congruence. rewrite <- Heqb. apply fold_constants_bexp_sound. apply IHc.
    + (* while a <= b *) apply CWhile_congruence. rewrite <- Heqb. apply fold_constants_bexp_sound. apply IHc.
    + (* while ~f *)     apply CWhile_congruence. rewrite <- Heqb. apply fold_constants_bexp_sound. apply IHc.
    + (* while p && f *) apply CWhile_congruence. rewrite <- Heqb. apply fold_constants_bexp_sound. apply IHc.
Qed.



Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | ANum n  => ANum n
  | AId x   => AId x
  | <{ 0 + a2 }> => optimize_0plus_aexp a2
  | <{ a1 + a2 }> =>
    match (optimize_0plus_aexp a1, optimize_0plus_aexp a2) with
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (optimize_0plus_aexp a1, optimize_0plus_aexp a2) with
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }> =>
    match (optimize_0plus_aexp a1, optimize_0plus_aexp a2) with
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>  => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> =>
      match (optimize_0plus_aexp a1, optimize_0plus_aexp a2) with
      | (a1', a2')         => <{ a1' = a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (optimize_0plus_aexp a1, optimize_0plus_aexp a2) with
      | (a1', a2')         => <{ a1' <= a2' }>
      end
  | <{ ~b1 }> =>
      match (optimize_0plus_bexp b1) with
      | b1'       =><{ ~b1' }>
      end
  | <{ b1 && b2 }> =>
      match (optimize_0plus_bexp b1, optimize_0plus_bexp b2) with
      | (b1', b2')              => <{ b1' && b2' }>
      end
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | <{ skip }>    => <{ skip }>
  | <{ x := a }>  => <{ x := (optimize_0plus_aexp a) }>
  | <{ c1 ; c2 }> => <{ optimize_0plus_com c1 ; optimize_0plus_com c2 }>
  | <{ if b then c1 else c2 end }> => <{ if optimize_0plus_bexp b then optimize_0plus_com c1 else optimize_0plus_com c2 end}>
  | <{ while b do c1 end }> => <{ while optimize_0plus_bexp b do (optimize_0plus_com c1) end }>
  end.

Example optimize_0plus_aexp_ex: optimize_0plus_aexp <{ 0 + X }> = <{ X }>.
Proof. reflexivity. Qed.

Example optimize_0plus_com_ex: 
  optimize_0plus_com <{ if (0 + X <= Y) then X := 0 + Y; Y := 0 + X else Y := 0 + 1 end }> =
  <{ if (X <= Y) then X := Y; Y := X else Y := 1 end }>.
Proof. reflexivity. Qed.

Theorem optimize_0plus_aexp_sound : atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intro a. unfold aequiv. intros st.
  induction a; simpl.
  - (* n *) reflexivity.
  - (* X *) reflexivity.
  - (* + *) 
    rewrite IHa1. rewrite IHa2.
    destruct a1 eqn:Ea1; try (reflexivity). (* match aexp, trivial for all except Nums *)
    destruct n eqn:En; simpl; reflexivity. (* match specific num *)
  - (* - *)
    rewrite IHa1. rewrite IHa2. reflexivity.
  - (* * *)
    rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem optimize_0plus_bexp_sound: btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intro b. unfold bequiv. intros st.
  induction b; simpl; 
    try (reflexivity);
    try ( rewrite (optimize_0plus_aexp_sound a1);
          rewrite (optimize_0plus_aexp_sound a2);
          reflexivity).
    try (rewrite IHb; reflexivity).
  - (* && *)
    rewrite IHb1.
    rewrite IHb2.
    reflexivity.
Qed.

Theorem optimize_0plus_com_sound : ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intro c. 
  induction c; unfold cequiv; intros st st'; simpl.
  - (* skip *) apply refl_cequiv.
  - (* :=   *) apply CAsgn_congruence. apply optimize_0plus_aexp_sound.
  - (* ;    *) apply CSeq_congruence.  apply IHc1. apply IHc2.
  - (* if   *) apply CIf_congruence. apply optimize_0plus_bexp_sound. apply IHc1. apply IHc2.
  - (* whle *) apply CWhile_congruence. apply optimize_0plus_bexp_sound. apply IHc.
Qed.



Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com. (* <--- NEW *)

Notation "'havoc' l"  := (CHavoc l)  (in custom com at level 60, l constr at level 0).
Notation "'skip'"     := CSkip       (in custom com at level 0).
Notation "x := y"     := (CAsgn x y) (in custom com at level 0, x constr at level 0, y at level 85, no associativity).
Notation "x ; y"      := (CSeq x y)  (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)  (in custom com at level 89, x at level 99, y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'"         := (CWhile x y) (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_Havoc (n: nat) : forall st x,
      st =[ CHavoc x ]=> (x !-> n ; st)

  where "st =[ c ]=> st'" := (ceval c st st').

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof. apply (E_Havoc 0). Qed.

Example havoc_example2 : empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof. apply (E_Seq _ _ empty_st empty_st (Z !-> 42)). apply E_Skip. apply (E_Havoc 42). Qed.

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

Definition pXY := <{ havoc X ; havoc Y }>.
Definition pYX := <{ havoc Y ; havoc X }>.

Theorem pXY_cequiv_pYX : cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof. unfold cequiv.
  unfold pXY. unfold pYX.
  left. intros st st'. split; intro H.
  - inversion H.
    inversion H5. 
    inversion H2.
    subst. 
    rewrite t_update_permute.
    apply (E_Seq _ _ st (Y !-> n; st) (X !-> n0; Y !-> n; st)).
    apply (E_Havoc n).
    apply (E_Havoc n0).
    unfold not.
    intros Hd. discriminate Hd.
  - inversion H.
    inversion H5. 
    inversion H2.
    subst. 
    rewrite t_update_permute.
    apply (E_Seq _ _ st (X !-> n; st) (Y !-> n0; X !-> n; st)).
    apply (E_Havoc n).
    apply (E_Havoc n0).
    unfold not.
    intros Hd. discriminate Hd. Qed.


Definition ptwice := <{ havoc X; havoc Y }>.
Definition pcopy  := <{ havoc X; Y := X }>.

Theorem ptwice_cequiv_pcopy : cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. unfold cequiv, ptwice, pcopy, not. right. intro H.
  destruct (H empty_st (Y !-> 0; X !-> 1)).
  assert (G: empty_st =[ havoc X; havoc Y ]=> (Y !-> 0; X !-> 1)). {
    apply (E_Seq _ _ _ (X !-> 1) (Y !-> 0; X !-> 1)).
    apply (E_Havoc 1).
    apply (E_Havoc 0).
  }
  assert (G': empty_st =[ havoc X; Y := X ]=> (Y !-> 0; X !-> 1)). { apply (H0 G). }
  inversion G'.
  subst.
  inversion H7.
  assert (G1: forall x, (Y !-> n; st') x = (Y !-> 0; X !-> 1) x). { apply equal_f. assumption. }
  simpl in H6.
  assert (G2: st' X = 1). { apply (G1 X). }
  rewrite H6 in G2.
  assert (G3: n = 0). { unfold t_update in G1. remember (G1 Y) as k. simpl in k. apply k. }
  rewrite G2 in G3. discriminate G3.
Qed.




Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.
Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

Lemma p1_may_diverge : forall st st', st X <> 0 -> ~ st =[ p1 ]=> st'.
Proof. unfold not. intros st st' Hx0 H.
  remember p1 as k eqn:Ek.
  induction H; 
    try (discriminate Ek);
    try (subst).
  - (* E_WhileFalse *)
    unfold p1 in Ek.
    injection Ek as Ekb Ekc.
    rewrite -> Ekb in H.
    simpl in H.
    apply negb_false_iff in H.
    apply beq_nat_true in H.
    apply Hx0. apply H.
  - (* E_WhileTrue *)
    unfold p1 in Ek.
    injection Ek as Ekb Ekc.
    rewrite Ekb in H.
    simpl in H.
    rewrite -> negb_true_iff in H.
    assert (G: ~ (st' X = 0)). {
      unfold not. intro Hcont.
      subst. 
      inversion H0.
      subst. 
      inversion H7.
      simpl in H8.
      subst.
      unfold t_update in Hcont.
      simpl in Hcont.
      Search (?a + ?b = ?b + ?a).
      rewrite add_comm in Hcont.
      discriminate Hcont.
    }
    apply IHceval2.
    apply G.
    unfold p1. rewrite Ekb. rewrite Ekc.
    reflexivity.
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 -> ~ st =[ p2 ]=> st'.
Proof. unfold not. intros st st' Hx0 H.
  remember p2 as k eqn:Ek.
  induction H; 
    try (discriminate Ek);
    try (subst).
  - (* E_WhileFalse *)
    unfold p2 in Ek.
    injection Ek as Ekb Ekc.
    rewrite -> Ekb in H.
    simpl in H.
    apply negb_false_iff in H.
    apply beq_nat_true in H.
    apply Hx0. apply H.
  - (* E_WhileTrue *)
    unfold p2 in Ek.
    injection Ek as Ekb Ekc.
    rewrite Ekb in H.
    simpl in H.
    rewrite -> negb_true_iff in H.
    assert (G: ~ (st' X = 0)). {
      unfold not. intro Hcont.
      subst. 
      inversion H0.
      subst.
      apply Hx0. apply Hcont.
    }
    apply IHceval2.
    apply G.
    unfold p2. rewrite Ekb. rewrite Ekc.
    reflexivity.
Qed.

Search ((?x =? ?n) = true -> ?x = ?n).

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. unfold cequiv, p1, p2. intros st st'.
  destruct (st X =? 0) eqn:Hex.
  - (* X = 0 *)
    apply beq_nat_true in Hex.
    split; intro H.
    + inversion H; subst.
      * (* WhileFalse *) simpl in H4. apply negb_false_iff in H4.
        apply (E_WhileFalse ). simpl. apply negb_false_iff. apply H4.
      * (* WhileTrue *) simpl in H2. apply negb_true_iff in H2.
        rewrite Hex in H2. discriminate H2.
    + inversion H; subst.
      * (* WhileFalse *) simpl in H4. apply negb_false_iff in H4.
        apply (E_WhileFalse ). simpl. apply negb_false_iff. apply H4.
      * (* WhileTrue *) simpl in H2. apply negb_true_iff in H2.
        rewrite Hex in H2. discriminate H2.
  - apply beq_nat_false in Hex.
    split; intro H; exfalso.
    + apply (p1_may_diverge _ _ Hex H).
    + apply (p2_may_diverge _ _ Hex H).
Qed.



Definition p3 : com :=
  <{ Z := 1;
     while ~(X = 0) do
       havoc X;
       havoc Z
     end }>.
Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.
Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. unfold not, cequiv, p3, p4. intros H.
  destruct (H (X !-> 1) (Z !-> 42; X !-> 0)) as [H1 H2].
  clear H H2.
  remember (Z !-> 42; X !-> 0; Z !-> 1; X !-> 1) as finalState.
  assert (G: (X !-> 1) =[ Z := 1; while ~ X = 0 do havoc X; havoc Z end ]=> finalState). {
    apply (E_Seq _ _ _ (Z !-> 1; X !-> 1) _).
    apply (E_Asgn). reflexivity.
    apply (E_WhileTrue (Z !-> 1; X !-> 1) finalState finalState).
    - (* while cond *) simpl. reflexivity.
    - (* while body *) apply (E_Seq) with (X !-> 0; Z !-> 1; X !-> 1).
      apply (E_Havoc 0).
      rewrite HeqfinalState.
      apply (E_Havoc 42 (X !-> 0; Z !-> 1; X !-> 1) Z).
    - (* while newx step *)
      apply (E_WhileFalse). rewrite HeqfinalState. reflexivity.
  }
  assert (G'': finalState = (Z !-> 42; X !-> 0)). {
    rewrite HeqfinalState.
    apply functional_extensionality.
    intro x. unfold t_update.
    destruct (eqb_string Z x). reflexivity.
    destruct (eqb_string X x). reflexivity.
    reflexivity.
  }
  assert (G': (X !-> 1) =[ X := 0; Z := 1 ]=> (Z !-> 42; X !-> 0)). { 
    rewrite G'' in G.
    apply (H1 G). 
  }
  inversion G'. subst.
  inversion H5. subst. simpl in *.
  assert (Contra1: (Z !-> 1; st') Z = 1). { unfold t_update. simpl. reflexivity. }
  assert (Contra2: (Z !-> 1; st') Z = 42). { rewrite H6. unfold t_update. simpl. reflexivity. }
  rewrite Contra2 in Contra1.
  discriminate Contra1.
Qed.



Definition p5 : com := <{ while ~(X = 1) do havoc X end }>.
Definition p6 : com := <{ X := 1 }>.
Theorem p5_p6_equiv : cequiv p5 p6.
Proof. unfold cequiv, p5, p6. intros st st'. split; intro H.
  - remember <{ while ~ X = 1 do havoc X end }> as p5 eqn:Ep5.
    induction H;
      try (discriminate Ep5);
      try (injection Ep5 as Ep5b Ep5c).
    + (* WhileFalse *)
      rewrite Ep5b in H. simpl in H. apply negb_false_iff in H. apply beq_nat_true in H.
      assert (G: st = (X !-> 1; st)). { 
        apply functional_extensionality. 
        intro x. unfold t_update. 
        unfold eqb_string.
        destruct (string_dec X x) as [Ex' | Ex'] eqn:Ex; subst.
        apply H.
        reflexivity.
      }
      assert (G': (st =[ X := 1 ]=> st) = (st =[ X := 1 ]=> (X !-> 1; st))). { rewrite <- G. reflexivity. }
      rewrite -> G'.
      apply (E_Asgn). reflexivity.
    + (* WhileTrue *)
      rewrite Ep5b in H. simpl in H. apply negb_true_iff in H. apply beq_nat_false in H.
      assert (G: st' =[ X := 1 ]=> st''). {apply IHceval2. rewrite Ep5b. rewrite Ep5c. reflexivity. }
      clear IHceval1 IHceval2.
      rewrite Ep5c in H0. inversion H0. subst. 
      inversion G. subst. simpl.
      assert (G': (X !-> 1; X !-> n; st) = (X !-> 1; st)). {
        apply functional_extensionality. intro x.
        unfold t_update. unfold eqb_string.
        destruct (string_dec X x) as [Ex' | Ex'] eqn:Ex; subst.
        - reflexivity.
        - reflexivity.
      }
      rewrite G'.
      apply E_Asgn.
      reflexivity.
  - destruct (beval st <{ ~ X = 1 }>) eqn:Ex.
    + (* true *)
      (* apply negb_true_iff in Ex. apply beq_nat_false in Ex. *)
      apply (E_WhileTrue st (X !-> 1; st) st' _ _ Ex).
      apply (E_Havoc 1).
      inversion H. subst. simpl in *.
      apply (E_WhileFalse).
      simpl. reflexivity.
(*     + simpl in Ex. apply negb_false_iff in Ex. apply beq_nat_true in Ex. *)
    +
      inversion H. subst. simpl in *.
      apply negb_false_iff in Ex. apply beq_nat_true in Ex.
      assert (G: st = (X !-> 1; st)). {
        apply functional_extensionality. intro x.
        unfold t_update. unfold eqb_string.
        destruct (string_dec X x) as [Ex' | Ex'] eqn:Ex''; subst.
        - apply Ex.
        - reflexivity.
      }
      rewrite <- G.
      apply (E_WhileFalse).
      simpl. rewrite Ex. reflexivity.
Qed.

End Himp.

Module ImpFor.


Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CFor (cInit : com) (b : bexp) (cInc : com) (cBody : com).

Check com.
Check com_rect.
Check com_ind.
Check com_rec.
Check com_sind.

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Notation "'for(' cInit ';' b ';' cInc ')' '{' cBody '}'" :=
         (CFor cInit b cInc cBody)
            (in custom com at level 89, cInit at level 85, 
                                        b     at level 85,
                                        cInc  at level 89,
                                        cBody at level 85) : com_scope.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
 | E_ForFalse : forall st st1 b cInit cBody cInc,
      st  =[ cInit ]=> st1 ->
      beval st1 b = false ->
      st  =[ for(cInit ; b ; cInc) { cBody } ]=> st1
  | E_ForTrue : forall st st1 st2 st3 st4 b cInit cBody cInc,
      st  =[ cInit ]=> st1 ->
      beval st1 b = true ->
      st1  =[ cBody ]=> st2 ->
      st2  =[ cInc ]=> st3 ->
      st3 =[ for(skip ; b ; cInc) { cBody } ]=> st4 ->
      st  =[ for(cInit ; b ; cInc) { cBody } ]=> st4

  where "st =[ c ]=> st'" := (ceval c st st').


Definition p5 c1 b c2 c3 : com := <{ for(c1; b; c2) { c3 } }>.
Definition p6 c1 b c2 c3 : com := <{c1; while b do c3; c2 end }>.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state), (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').


Theorem p5_p6_equiv : forall c1 b c2 c3, cequiv (p5 c1 b c2 c3) (p6 c1 b c2 c3).
Proof. intros c1 b c2 c3. unfold cequiv. intros st st'. unfold p5, p6. split; intro H.
  - remember <{ for( c1; b; c2){c3} }> as forLoop eqn:Ef.
    generalize dependent c1.
    induction H; intros c1' Ef;
      try (discriminate Ef).
    + (* for false *) 
      injection Ef as Ef1 Ef2 Ef3 Ef4. 
        rewrite -> Ef1, Ef2 in *. clear Ef1 Ef2 Ef3 Ef4.
      apply (E_Seq _ _ st st1 st1 H).
      apply (E_WhileFalse _ _ _ H0).
    + (* for true *)
      injection Ef as Ef1 Ef2 Ef3 Ef4. 
        rewrite -> Ef1, Ef2, Ef3, Ef4 in *. clear Ef1 Ef2 Ef3 Ef4 IHceval1 IHceval2 IHceval3.
      apply (E_Seq _ _ st st1 st4 H).
      apply (E_WhileTrue _ st3 _ b _ H0).
        apply (E_Seq _ _ _ _ _ H1 H2).
      assert (G: st3 =[ skip; while b do c3; c2 end ]=> st4). {
        apply (IHceval4 <{ skip }>).
        reflexivity.
      }
      inversion G.
      inversion H6. subst.
      apply H9.
  - remember <{ c1; while b do c3; c2 end }> eqn:Ef.
    destruct H;
      try (discriminate Ef).
    injection Ef as Ef1 Ef2.
      rewrite -> Ef1 in *. clear Ef1.
    generalize dependent c1.
    generalize dependent st.
    induction H0; intros stk c1' Ec1;
      try (discriminate Ef2).
    + injection Ef2 as Ef1 Ef2.
        rewrite -> Ef1 in *.
      apply (E_ForFalse stk st _ _ _ _ Ec1 H).
    + injection Ef2 as Ef21 Ef22.
        rewrite -> Ef21 in *. clear Ef21. rewrite -> Ef22 in *. clear Ef22.
      inversion H0_. subst.
      apply (E_ForTrue stk st st'0 st' _ _ _ _ _ Ec1 H H2 H5).
      assert (G: forall st c1, st =[ c1 ]=> st' -> st =[ for( c1; b; c2){c3} ]=> st''). { apply IHceval2. reflexivity. }
      apply (G st' <{ skip }>).
      apply E_Skip.
Qed.


End ImpFor.

