Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

 Inductive tm : Type :=
  | C : nat -> tm        (* Constant *)
  | P : tm  -> tm -> tm. (* Plus *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n   => n
  | P a b => evalF a + evalF b
  end.

Reserved Notation " t '==>' n " (at level 50, left associativity).
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)
where " t '==>' n " := (eval t n).



Module SimpleArith1.
  Reserved Notation " t '-->' t' " (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_PlusConstConst : forall n m,
        P (C n) (C m) --> C (n + m)
    | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
    | ST_Plus2 : forall n t2 t2',
        t2 --> t2' ->
        P (C n) t2 --> P (C n) t2'
    where " t '-->' t' " := (step t t').

   Example test_step_2 :
        P
          (C 0)
          (P
            (C 2)
            (P (C 1) (C 3)))
        -->
        P
          (C 0)
          (P
            (C 2)
            (C 4)).
  Proof.
    apply ST_Plus2.
    apply ST_Plus2.
    apply ST_PlusConstConst.
  Qed.
End SimpleArith1.


(* See Rel.v in vol1 *)
Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=  forall x y1 y2 : X, 
  R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
  Import SimpleArith1.
  Theorem step_deterministic:  deterministic step.
  Proof.
    unfold deterministic. intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    induction Hy1; intros y2 Hy2.
    - (* ST_PlusConstConst *) inversion Hy2; subst.
      + (* ST_PlusConstConst *) reflexivity.
      + (* ST_Plus1 *) inversion H2.
      + (* ST_Plus2 *) inversion H2.
    - (* ST_Plus1 *) inversion Hy2; subst.
      + (* ST_PlusConstConst *)
        inversion Hy1.
      + (* ST_Plus1 *)
        apply IHHy1 in H2. rewrite H2. reflexivity.
      + (* ST_Plus2 *)
        inversion Hy1.
    - (* ST_Plus2 *) inversion Hy2; subst.
      + (* ST_PlusConstConst *)
        inversion Hy1.
      + (* ST_Plus1 *) inversion H2.
      + (* ST_Plus2 *)
        apply IHHy1 in H2. rewrite H2. reflexivity.
  Qed.
End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with 
  | H : ?T |- _ =>
    match type of T with 
    | Prop =>
      solve [
        inversion H;
        match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
    end 
  end.

Ltac solve_by_invert :=  solve_by_inverts 1.

Module SimpleArith3.
  Import SimpleArith1.
  Theorem step_deterministic_alt: deterministic step.
  Proof.
    intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    induction Hy1; intros y2 Hy2;
      inversion Hy2; subst; try solve_by_invert.
    - (* ST_PlusConstConst *) reflexivity.
    - (* ST_Plus1 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
    - (* ST_Plus2 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
  Qed.
End SimpleArith3.



Inductive value : tm -> Prop :=
  | v_const: forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n m,
          P (C n) (C m) --> C (n + m)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' -> P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v t2 t2',
        value v ->
        t2 --> t2' ->
        P v t2 --> P v t2'
  where " t '-->' t' " := (step t t').

Theorem step_deterministic :  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 H1 H2.
  generalize dependent y2.
  induction H1; intros y2 H2.
  - inversion H2; subst.
    + reflexivity.
    + inversion H3.
    + inversion H4.
  - inversion H2; subst.
    + inversion H1.
    + assert (G: t1' = t1'0). {
        apply IHstep.
        apply H4.
      }
      rewrite G.
      reflexivity.
    + inversion H3; subst.
      inversion H1.
  - inversion H2; subst.
    + inversion H1.
    + inversion H; subst.
      inversion H5.
    + assert (G: t2' = t2'0). {
        apply IHstep.
        apply H6.
      }
      rewrite G. reflexivity.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  intro t.
  induction t.
  - left. apply v_const.
  - right.
    destruct IHt1 as [Ht1Val | Ht1Red].
    + inversion Ht1Val; subst.
      destruct IHt2 as [Ht2Val | Ht2Red].
      * inversion Ht2Val; subst.
        eexists.
        apply ST_PlusConstConst.
      * destruct Ht2Red as [t' Ht'].
        eexists.
        apply ST_Plus2.
        apply Ht1Val.
        apply Ht'.
    + destruct Ht1Red as [t' Ht'].
      eexists.
      apply ST_Plus1.
      apply Ht'.
Qed.


Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~(exists t', R t t').

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  intros v H H1.
  inversion H.
  subst.
  destruct H1 as [t' H1'].
  inversion H1'.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.




Module Temp1.
  Inductive value : tm -> Prop :=
    | v_const : forall n, value (C n)
    | v_funny : forall t1 n2, (* <--- NEW *)
                  value (P t1 (C n2)).
  Reserved Notation " t '-->' t' " (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_PlusConstConst : forall n1 n2,
        P (C n1) (C n2) --> C (n1 + n2)
    | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
    | ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'
    where " t '-->' t' " := (step t t').

  Lemma value_not_same_as_normal_form :
    exists v, value v /\ ~ normal_form step v.
  Proof.
    exists (P (C 0) (C 0)).
    split.
    - apply v_funny.
    - intro Hcontra. unfold normal_form in Hcontra.
      apply Hcontra.
      exists (C 0).
      apply ST_PlusConstConst.
  Qed.
End Temp1.

Module Temp2.
  Inductive value : tm -> Prop :=
    | v_const : forall n, value (C n). (* Original definition *)

  Reserved Notation " t '-->' t' " (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_Funny : forall n,
        C n --> P (C n) (C 0) (* <--- NEW *)
    | ST_PlusConstConst : forall n1 n2,
        P (C n1) (C n2) --> C (n1 + n2)
    | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
    | ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'
    where " t '-->' t' " := (step t t').

  Lemma value_not_same_as_normal_form :
    exists v, value v /\ ~normal_form step v.
  Proof.
    exists (C 0).
    split.
    - apply v_const.
    - intro HContra. apply HContra.
      exists (P (C 0) (C 0)).
      apply ST_Funny.
  Qed.
End Temp2.

Module Temp3.
  Inductive value : tm -> Prop :=
    | v_const : forall n, value (C n).

  Reserved Notation " t '-->' t' " (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_PlusConstConst : forall n1 n2,
        P (C n1) (C n2) --> C (n1 + n2)
    | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
    where " t '-->' t' " := (step t t').

  Lemma value_not_same_as_normal_form :
    exists t, ~ value t /\ normal_form step t.
  Proof.
    exists (P (C 0) (P (C 0) (C 0))).
    split.
    - intros HContra. inversion HContra.
    - intros HContra. destruct HContra as [t' HContra].
      inversion HContra; subst. inversion H2.
  Qed. 
End Temp3.

Module Temp4.
  Inductive tm : Type :=
    | tru : tm
    | fls : tm
    | test : tm -> tm -> tm -> tm.
  Inductive value : tm -> Prop :=
    | v_tru : value tru
    | v_fls : value fls.

  Reserved Notation " t '-->' t' " (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_IfTrue : forall t1 t2,
        test tru t1 t2 --> t1
    | ST_IfFalse : forall t1 t2,
        test fls t1 t2 --> t2
    | ST_If : forall t1 t1' t2 t3,
        t1 --> t1' ->
        test t1 t2 t3 --> test t1' t2 t3
    where " t '-->' t' " := (step t t').

  (* Definition bool_step_prop1 :=  fls --> fls. *)
  (*
  Definition bool_step_prop2 :=
       test
         tru
         (test tru tru tru)
         (test fls fls fls)
    -->
       tru.
  *)
  (*
  Definition bool_step_prop3 :=
       test
         (test tru tru tru)
         (test tru tru tru)
         fls
     -->
       test
         tru
         (test tru tru tru)
         fls.
  *)

  Theorem strong_progress_bool : forall t,
    value t \/ (exists t', t --> t').
  Proof.
    intro t. induction t.
    - left. constructor.
    - left. constructor.
    - right.
      destruct t1.
      + eexists. apply ST_IfTrue.
      + eexists. apply ST_IfFalse.
      + destruct IHt1 as [Hl | Hr].
        * inversion Hl.
        * destruct Hr as [t' Hr].
          exists (test t' t2 t3).
          apply ST_If. assumption.
  Qed.

  Lemma test_true: forall t f x, test tru t f --> x -> x = t.
  Proof.
    intros t f x H.
    inversion H; subst.
    - reflexivity.
    - inversion H4.
  Qed.

  Lemma test_false: forall t f x, test fls t f --> x -> x = f.
  Proof.
    intros t f x H.
    inversion H; subst.
    - reflexivity.
    - inversion H4.
  Qed.

  Theorem step_deterministic :
    deterministic step.
  Proof.
    unfold deterministic. intro x. induction x; intros y1 y2 H1 H2.
    - inversion H1; subst.
    - inversion H1; subst.
    - destruct x1; subst.
      + (* x1 = true *) 
        rewrite (test_true _ _ _ H1).
        rewrite (test_true _ _ _ H2).
        reflexivity.
      + (* x1 = false *) 
        rewrite (test_false _ _ _ H1).
        rewrite (test_false _ _ _ H2).
        reflexivity.
      + inversion H1; subst. inversion H2; subst.
        assert (G: t1' = t1'0). {
          apply IHx1. apply H5. apply H6.
        }
        rewrite G. reflexivity.
  Qed.

  Module Temp5.
    Reserved Notation " t '-->' t' " (at level 40).
    Inductive step : tm -> tm -> Prop :=
      | ST_IfTrue : forall t1 t2,
          test tru t1 t2 --> t1
      | ST_IfFalse : forall t1 t2,
          test fls t1 t2 --> t2
      | ST_If : forall t1 t1' t2 t3,
          t1 --> t1' ->
          test t1 t2 t3 --> test t1' t2 t3
      | ST_ShortCircuit : forall t1 t2,
          test t1 t2 t2 --> t2
      where " t '-->' t' " := (step t t').

    Definition bool_step_prop4 :=
             test
                (test tru tru tru)
                fls
                fls
         -->
             fls.
    Example bool_step_prop4_holds :
      bool_step_prop4.
    Proof.
      unfold bool_step_prop4.
      apply ST_ShortCircuit.
    Qed.

    Theorem step_with_short_circ_not_deterministic :
      ~(deterministic step).
    Proof.
      unfold deterministic.
      intro H.
      assert (G: fls = test tru fls fls). {
        apply H with (x := test (test tru tru tru) fls fls).
        - apply ST_ShortCircuit.
        - apply ST_If. apply ST_IfTrue.
      }
      inversion G.
    Qed.

    Theorem strong_progress_bool : forall t,
      value t \/ (exists t', t --> t').
    Proof.
      intro t. induction t.
      - left. constructor.
      - left. constructor.
      - right.
        destruct t1.
        + eexists. apply ST_IfTrue.
        + eexists. apply ST_IfFalse.
        + destruct IHt1 as [Hl | Hr].
          * inversion Hl.
          * destruct Hr as [t' Hr].
            exists (test t' t2 t3).
            apply ST_If. assumption.
    Qed.
  End Temp5.
End Temp4.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), 
                    multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof. intros X R x y H. 
  apply (multi_step R x y y H).
  apply multi_refl.
Qed.


Theorem multi_trans :  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z H1 H2.
  induction H1.
  - (* refl *)apply H2.
  - (* step *)apply multi_step with y.
    apply H.
    apply IHmulti.
    apply H2.
Qed.

Print multi_trans.
Print multi_ind.


Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with (P (C (0 + 3)) (P (C 2) (C 4))).
  { apply ST_Plus1. apply ST_PlusConstConst. }
  apply multi_step with (P (C (0 + 3)) (C (2 + 4))).
  { apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  apply multi_R.
  apply ST_PlusConstConst.
Qed.

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_PlusConstConst. }
  apply multi_refl.
Qed.

Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  apply multi_refl.
Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  apply multi_refl.
Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  apply multi_step with (P
        (C 0)
        (P
          (C 2)
          (C (0 + 3)))). { apply ST_Plus2. apply v_const. apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  apply multi_refl.
Qed.


Definition step_normal_form := normal_form step.
Definition normal_form_of (t t' : tm) :=  (t -->* t' /\ step_normal_form t').

Theorem normal_forms_unique:  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  induction P11.
  - inversion P21; subst.
    + reflexivity.
    + exfalso. apply P12. exists y. assumption.
  - inversion P21; subst.
    + exfalso. apply P22. exists y. assumption.
    + assert (G: y = y0). { apply (step_deterministic _ _ _ H H0). }
      apply IHP11.
      apply P12.
      rewrite G.
      assumption.
Qed.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.


Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H.
  induction H.
  - (* refl *) apply multi_refl.
  - apply multi_step with (P y t2). apply ST_Plus1. apply H.
    assumption.
Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 -->* t2' ->
     P t1 t2 -->* P t1 t2'.
Proof.
  intros t1 t2 t2' Hv H.
  induction H.
  - (* refl *) apply multi_refl.
  - apply multi_step with (P t1 y). apply ST_Plus2. apply Hv. apply H.
    assumption.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* We can use rewrite with "iff" statements, not
           just equalities: *)
      apply nf_same_as_value. apply v_const.
  - (* P *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1] ].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2] ].
    apply nf_same_as_value in Hnormal1.
    apply nf_same_as_value in Hnormal2.
    destruct Hnormal1 as [n1].
    destruct Hnormal2 as [n2].
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with (P (C n1) (C n2)).
        { apply multistep_congr_2. apply v_const. apply Hsteps2. }
        apply multi_R. apply ST_PlusConstConst.
    + (* r *)
      apply nf_same_as_value. apply v_const.
Qed.

Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.
Proof.
  intros t n H.
  induction H.
  - apply multi_refl.
  - induction t1.
    + (* const *) induction t2.
      * (* const *) 
        inversion IHeval1; subst.
        inversion IHeval2; subst.
        eapply multi_step. apply ST_PlusConstConst. apply multi_refl.
        inversion H0; subst. eapply multi_step. apply ST_PlusConstConst. apply multi_refl.
        inversion H0; subst. inversion H; subst. eapply multi_step. apply ST_PlusConstConst. apply multi_refl.
      * (* _ + _ *)
        inversion H; subst.
        assert (G: P (C n1) (P t2_1 t2_2) -->* P (C n1) (C n2)). {
          apply multistep_congr_2.
          apply v_const.
          apply IHeval2.
        }
        apply multi_trans with (P (C n1) (C n2)).
        apply G.
        eapply multi_step. apply ST_PlusConstConst. apply multi_refl.
    + (* _ + _ *)
      assert (G: P (P t1_1 t1_2) t2 -->* P (C n1) t2). {
        apply multistep_congr_1.
        apply IHeval1.
      }
      apply multi_trans with (P (C n1) t2).
      apply G.
      assert (G': P (C n1) t2 -->* P (C n1) (C n2)). {
        apply multistep_congr_2. 
        apply v_const.
        apply IHeval2.
      }
      apply multi_trans with (P (C n1) (C n2)).
      apply G'.
      eapply multi_step. apply ST_PlusConstConst. apply multi_refl.
Qed.


Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs.
  - intros k H.
    inversion H; subst.
    apply E_Plus.
    + constructor.
    + constructor.
  - intros n H.
    inversion H; subst.
    apply E_Plus.
    + apply IHHs. assumption.
    + assumption.
  - intros n H'.
    inversion H'; subst.
    apply E_Plus.
    + assumption.
    + apply IHHs. assumption.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  intro t.
  induction t; intros t' Hn; unfold normal_form_of in Hn; destruct Hn as [Hnl Hnr].
  - exists n.
    split.
    + inversion Hnl; subst; try reflexivity.
      inversion H.
    + constructor.
  -
    assert (G1: exists n1, t1 ==> n1). {
      destruct (step_normalizing t1) as [a [b c]].
      destruct (IHt1 a).
      split. apply b. apply c.
      destruct H. exists x. assumption.
    }
    assert (G2: exists n2, t2 ==> n2). {
      destruct (step_normalizing t2) as [a [b c]].
      destruct (IHt2 a).
      split. apply b. apply c.
      destruct H. exists x. assumption.
    }
    clear IHt1 IHt2.
    destruct G1 as [n1 H1].
    destruct G2 as [n2 H2].
    exists (n1 + n2). split; try reflexivity.
    + apply eval__multistep in H1.
      apply eval__multistep in H2.
      assert (G: P t1 t2 -->* P (C n1) t2). {
        apply multistep_congr_1.
        apply H1.
      }
      assert (G1: P (C n1) t2 -->* P (C n1) (C n2)). {
        apply multistep_congr_2.
        constructor.
        apply H2.
      }
      assert (G2: P t1 t2 -->*P (C n1) (C n2)). {
        eapply multi_trans.
        apply G.
        apply G1.
      }
      assert (G3: P t1 t2 -->* C (n1 + n2)). {
        eapply multi_trans.
        apply G2.
        eapply multi_step. constructor. eapply multi_refl.
      }
      assert (G5: t' = C (n1 + n2)). {
        apply (normal_forms_unique (P t1 t2)).
        - split. apply Hnl. apply Hnr.
        - split. apply G3. 
          unfold step_normal_form, normal_form.
          intros [a b]. inversion b.
      }
      apply G5.
    + constructor. assumption. assumption.
Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  intros t n. split; intro H.
  generalize dependent n.
  - induction t.
    + intros n' H. simpl in H; subst. constructor.
    + intros n H. simpl in H.
      rewrite <- H.
      apply (E_Plus t1 t2).
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
  - induction H.
    + reflexivity.
    + simpl. auto.
Qed.



Module Combined.
Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  where " t '-->' t' " := (step t t').


Theorem combined_deterministic: deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 H1 H2.
  generalize dependent y2.
  induction H1; intros y2 H2.
  - (*ST_PlusConstConst*) inversion H2; subst.
    + reflexivity.
    + inversion H3.
    + inversion H4.
  - (* ST_Plus1 *) inversion H2; subst.
    + inversion H1.
    + apply IHstep in H4. subst. reflexivity.
    + inversion H3; subst. inversion H1. inversion H1. inversion H1.
  - (* ST_Plus2 *) inversion H; subst.
    + inversion H2; subst. 
      * inversion H1.
      * inversion H5.
      * inversion H2; subst. inversion H3.
        apply IHstep in H8; subst. reflexivity.
    + inversion H2. inversion H5; subst.
      apply IHstep in H6. subst. reflexivity.
    + inversion H2. inversion H5; subst.
      apply IHstep in H6. subst. reflexivity.
  - (* ST_IfTrue *) inversion H2; subst. reflexivity. inversion H4.
  - (* ST_IfFalse *) inversion H2; subst. reflexivity. inversion H4.
  - (* ST_If *) inversion H2; subst.
    + inversion H1.
    + inversion H1.
    + apply IHstep in H5. subst. reflexivity.
Qed.
End Combined.




Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).


Reserved Notation " a '/' st '-->a' a' " (at level 40, st at level 39).
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }> / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (n1 n2 : nat),
      <{ n1 + n2 }> / st -->a (n1 + n2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }> / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (n1 n2 : nat),
      <{ n1 - n2 }> / st -->a (n1 - n2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }> / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (n1 n2 : nat),
      <{ n1 * n2 }> / st -->a (n1 * n2)
  where " a '/' st '-->a' a' " := (astep st a a').

Reserved Notation " b '/' st '-->b' b' " (at level 40, st at level 39).
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
  | BS_Eq1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
  | BS_Eq2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
  | BS_Eq : forall (n1 n2 : nat),
      <{ n1 = n2 }> / st -->b
      (if (n1 =? n2) then <{ true }> else <{ false }>)
  | BS_LtEq1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
  | BS_LtEq2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
  | BS_LtEq : forall (n1 n2 : nat),
      <{ n1 <= n2 }> / st -->b
      (if (n1 <=? n2) then <{ true }> else <{ false }>)
  | BS_NotStep : forall b1 b1',
      b1 / st -->b b1' ->
      <{ ~b1 }> / st -->b <{ ~b1' }>
  | BS_NotTrue : <{ ~true }> / st -->b <{ false }>
  | BS_NotFalse : <{ ~false }> / st -->b <{ true }>
  | BS_AndStep : forall b1 b1' b2,
      b1 / st -->b b1' ->
      <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
  | BS_AndTrueStep : forall b2 b2',
      b2 / st -->b b2' ->
      <{ true && b2 }> / st -->b <{ true && b2' }>
  | BS_AndFalse : forall b2,
      <{ false && b2 }> / st -->b <{ false }>
  | BS_AndTrueTrue : <{ true && true }> / st -->b <{ true }>
  | BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>
where " b '/' st '-->b' b' " := (bstep st b b').



Reserved Notation " t '/' st '-->' t' '/' st' "    (at level 40, st at level 39, t' at level 39).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st  -->  <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st  -->  <{ if b1 then c1; while b1 do c1 end else skip end }> / st
where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

