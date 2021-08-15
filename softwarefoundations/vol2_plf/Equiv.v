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
