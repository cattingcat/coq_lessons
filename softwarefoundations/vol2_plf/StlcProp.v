Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.

Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  empty |- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof. intros t Ht Hv.
  inversion Hv.
  - subst. inversion Ht.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof. intros t T1 T2 Ht Hv.
  inversion Hv; subst.
  - exists x0, t1. inversion Ht; subst. reflexivity.
  - inversion Ht. 
  - inversion Ht. 
Qed.

Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof. intros t T Ht.
  remember empty as e eqn:Ee.
  induction Ht; subst.
  - (*var*) discriminate H.
  - (*abs*) left. constructor.
  - (*app*)
    destruct IHHt1; try reflexivity.
    + (*t1 value*)
      destruct IHHt2; try reflexivity.
      * (*t2 value*)
        right. 
        inversion H; subst; try (inversion Ht1; subst). 
        exists <{ [x0:=t2]t0 }>. 
        apply ST_AppAbs. 
        assumption.
      * (*t2 progress*)
        right.
        destruct H0 as [t' Hr].
        exists <{t1 t'}>.
        apply ST_App2.
        apply H.
        apply Hr.
    + (*t1 progress*)
      right.
      destruct H as [t' Hr].
      exists <{t' t2}>.
      apply ST_App1.
      apply Hr.
  - (*true*) left. constructor.
  - (*false*) left. constructor.
  - (*if*)
    right.
    destruct IHHt1; try reflexivity.
    + (*t1 val*) 
      inversion H; subst; try (inversion Ht1; subst).
      * eexists. apply ST_IfTrue. 
      * eexists. apply ST_IfFalse. 
    + (*t1 progr*) destruct H as [t' H]. eexists.
      apply ST_If. apply H.
Qed.

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  - (*var*) inversion Ht. discriminate H1.
  - (*app*) inversion Ht; subst. 
    destruct (IHt1 _ H2).
    + (*t1 val*) destruct (IHt2 _ H4).
      * (*t2 val*) inversion H; subst; try (inversion H2; subst).
        right.
        exists <{ [x0:=t2]t0 }>.
        constructor. assumption.
      * (*t2 progr*) right.
        destruct H0 as [t' Ht'].
        exists <{ t1 t' }>.
        apply ST_App2. assumption.
        apply Ht'.
    + (*t1 progr*)
      destruct H as [t' Ht'].
      right. exists <{ t' t2 }>.
      apply ST_App1. assumption.
  - (*if*)
    right.
    inversion Ht; subst.
    destruct (IHt1 <{Bool}>); try assumption.
    + (*t1 val*) 
      inversion H; subst; try (inversion H3; subst).
      * eexists. apply ST_IfTrue. 
      * eexists. apply ST_IfFalse. 
    + (*t1 progr*) destruct H as [t' H]. eexists.
      apply ST_If. apply H.
Qed.



Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma |- t \in T ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |-  t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T  ->
  empty |- v \in U  ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - rename x0 into y. destruct (eqb_stringP x y); subst.
    + rewrite update_eq in H. injection H as H'. subst. apply weakening_empty. assumption.
    + rewrite update_neq in H. constructor. assumption.
      assumption.
  - rename x0 into y. destruct (eqb_stringP x y); subst.
    + apply T_Abs.
      rewrite update_shadow in Ht. assumption.
    + apply T_Abs.
      apply IHHt.
      rewrite update_permute; auto.
Qed.


Theorem preservation : forall t t' T,
  empty |- t \in T ->
  t --> t' ->
  empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and eauto takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.

Definition stuck (t:tm) : Prop :=  (normal_form step) t /\ ~(value t).
Corollary type_soundness : forall t t' T,
  empty |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - apply progress in Hhas_type.
    destruct Hhas_type as [Hval | Hprogr].
    + apply Hnot_val. assumption.
    + apply Hnf. assumption.
  - apply IHHmulti; try assumption.
    apply preservation with x0; try assumption.
Qed.


Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T  ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
  intros G e.
  generalize dependent G.
  induction e; intros G T T' H H'.
  - (*var*) inversion H; subst. inversion H'; subst.
    rewrite H2 in H3. injection H3 as H3. assumption.
  - (*app*) inversion H; subst. inversion H'; subst.
    assert (Hg: (<{T2 -> T}>) = (<{T0 -> T'}>)). {
      apply (IHe1 G). assumption. assumption.
    }
    injection Hg as Hg1 Hg2.
    assumption.
  - (*abs*) inversion H; subst. inversion H'; subst.
    assert (Hg: T1 = T0). {
      eapply IHe.
      apply H5.
      apply H6.
    }
    rewrite Hg.
    reflexivity.
  - (*true*) inversion H; subst. inversion H'; subst.
    reflexivity.
  - (*false*) inversion H; subst. inversion H'; subst.
    reflexivity.
  - (*if*) inversion H; subst. inversion H'; subst.
    apply (IHe2 G).
    assumption.
    assumption.
Qed.




Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>.
Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=   forall x, ~(appears_free_in x t).

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T G H.
  generalize dependent G.
  generalize dependent T.
  induction H; intros T G Ht; inversion Ht; subst.
  - exists T.  assumption.
  - apply IHappears_free_in in H3. assumption.
  - apply IHappears_free_in in H5. assumption.
  - apply IHappears_free_in in H6. rewrite update_neq in H6.
    assumption.
    assumption.
  - apply IHappears_free_in in H4. assumption.
  - apply IHappears_free_in in H6. assumption.
  - apply IHappears_free_in in H7. assumption.
Qed.

Corollary typable_empty__closed : forall t T,
    empty |- t \in T ->
    closed t.
Proof.
  intros t T Ht x Hfr.
  inversion Ht; subst.
  - discriminate H.
  - inversion Hfr; subst.
    destruct (free_in_context _ _ _ _ H4 H) as [T' Hgt'].
    rewrite update_neq in Hgt'.
    + discriminate Hgt'.
    + assumption.
  - inversion Hfr; subst.
    + destruct (free_in_context _ _ _ _ H2 H) as [T' Hgt'].
      discriminate Hgt'.
    + destruct (free_in_context _ _ _ _ H2 H0) as [T' Hgt'].
      discriminate Hgt'.
  - inversion Hfr.
  - inversion Hfr.
  - inversion Hfr; subst.
    + destruct (free_in_context _ _ _ _ H3 H) as [T' Hgt'].
      discriminate Hgt'.
    + destruct (free_in_context _ _ _ _ H3 H0) as [T' Hgt'].
      discriminate Hgt'.
    + destruct (free_in_context _ _ _ _ H3 H1) as [T' Hgt'].
      discriminate Hgt'.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof.
  intros G G' t T Ht.
  generalize dependent G'.
  induction Ht; intros G' F.
  - constructor.
    rewrite <- (F x0).
      assumption.
      constructor.
  - apply T_Abs.
    apply IHHt.
    intros x' Hx'.
    destruct (eqb_stringP x0 x').
    + subst. rewrite update_eq. rewrite update_eq. reflexivity.
    + rewrite update_neq; try apply n.
      rewrite update_neq; try apply n.
      apply (F x').
      constructor.
        apply n.
        assumption.
  - apply T_App with T2.
    + apply IHHt1. intros x' H'. apply F. apply afi_app1. assumption.
    + apply IHHt2. intros x' H'. apply F. apply afi_app2. assumption.
  - constructor.
  - constructor.
  - constructor.
    + apply IHHt1. intros x' H'. apply F. apply afi_if1. assumption.
    + apply IHHt2. intros x' H'. apply F. apply afi_if2. assumption.
    + apply IHHt3. intros x' H'. apply F. apply afi_if3. assumption.
Qed.

(*TODO ex *)

End STLCProp.



Module STLCArith.
Import STLC.

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat : ty.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99, t custom stlc at level 99, y custom stlc at level 99, left associativity).
Coercion tm_var : string >-> tm.
Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89, x custom stlc at level 99, y custom stlc at level 99, z custom stlc at level 99, left associativity).
Coercion tm_const : nat >-> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{ \x:T2, t1 }>
  | v_nat : forall (x: nat),
      value <{ x }>.
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{t1 t2}> => <{([x:=s] t1) ([x:=s] t2)}>
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | tm_const n => tm_const n
  | <{succ t}> => <{succ ([x:=s]t)}>
  | <{pred t}> => <{pred ([x:=s]t)}>
  | <{t1 * t2}> => <{([x:=s]t1) * ([x:=s]t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>

  | ST_Pred : forall t t',
        t --> t' ->
         <{pred t}> --> <{pred t'}>
  | ST_Pred_0 :
         <{pred 0}> --> <{0}>
  | ST_Pred_s : forall (t: nat), 
         tm_pred (tm_const (S t)) --> <{t}>

  | ST_Succ : forall t t',
        t --> t' ->
         <{succ t}> --> <{succ t'}>
  | ST_Succ_const : forall (n : nat), 
         <{succ n}> --> tm_const (S n)

  | ST_MulConst : forall (n m : nat),
         <{ n * m }> --> tm_const (n * m)
  | ST_Mul1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mul2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>

  | ST_IfTrue : forall t1 t2,
      <{if0 0 then t1 else t2}> --> t1
  | ST_IfFalse : forall n t1 t2,
      n <> 0 ->
      <{if0 n then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
where "t '-->' t'" := (step t t').
Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).



Definition context := partial_map ty.
Reserved Notation "Gamma '|-' t '\in' T"
            (at level 101, t custom stlc, T custom stlc at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_Const : forall Gamma (n: nat),
       Gamma |- n \in Nat
  | T_Succ : forall Gamma t,
       Gamma |- t \in Nat ->
       Gamma |- succ t \in Nat
  | T_Pred : forall Gamma t,
       Gamma |- t \in Nat ->
       Gamma |- pred t \in Nat
  | T_Mult : forall t1 t2 Gamma,
       Gamma |- t1 \in Nat ->
       Gamma |- t2 \in Nat ->
       Gamma |- t1 * t2 \in Nat
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Nat ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if0 t1 then t2 else t3 \in T1
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.


Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_succ : forall t,
      appears_free_in x t ->
      appears_free_in x <{succ t}>
  | afi_pred : forall t,
      appears_free_in x t ->
      appears_free_in x <{pred t}>
  | afi_mult1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 * t2}>
  | afi_mult2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 * t2}>.
Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=   forall x, ~(appears_free_in x t).

Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma |- t \in T ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |-  t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros G x U t.
  generalize dependent G.
  generalize dependent x.
  generalize dependent U.
  induction t; intros U x G v T Ht Hv; simpl.
  - (*| tm_var *)
    destruct (eqb_stringP x s); subst.
    + inversion Ht; subst.
      rewrite update_eq in H1.
      injection H1 as H1; subst.
      apply weakening_empty.
      assumption.
    + inversion Ht; subst.
      rewrite update_neq in H1; try (apply n).
      constructor.
      assumption.
  - (*| tm_app *)
    inversion Ht; subst.
    eapply T_App.
    + apply IHt1 with U; try (apply Hv).
      apply H2.
    + apply IHt2 with U; try (apply Hv).
      apply H4.
  - (*| tm_abs *)
    inversion Ht; subst.
    destruct (eqb_stringP x s); subst.
    + apply T_Abs.
      rewrite update_shadow in H4.
      assumption.
    + apply T_Abs.
      apply IHt with U; try (apply Hv).
      rewrite update_permute.
        assumption.
        intro Hc. symmetry in Hc. apply n. apply Hc.
  - (*| tm_const *)
    inversion Ht; subst.
    constructor.
  - (*| tm_succ *)
    inversion Ht; subst.
    constructor.
    apply IHt with U; try (apply Hv).
    assumption.
  - (*| tm_pred *)
    inversion Ht; subst.
    constructor.
    apply IHt with U; try (apply Hv).
    assumption.
  - (*| tm_mult *)
    inversion Ht; subst.
    eapply T_Mult.
    + apply IHt1 with U; try (apply Hv).
      apply H2.
    + apply IHt2 with U; try (apply Hv).
      apply H4.
  - (*| tm_if0 *)
    inversion Ht; subst.
    eapply T_If.
    + apply IHt1 with U; try (apply Hv).
      apply H3.
    + apply IHt2 with U; try (apply Hv).
      apply H5.
    + apply IHt3 with U; try (apply Hv).
      apply H6.
Qed.

Theorem preservation : forall t t' T,
  empty |- t \in T ->
  t --> t' ->
  empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and eauto takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.


(*
  | T_Var : forall Gamma x T1,
  | T_Abs : forall Gamma x T1 T2 t1,
  | T_App : forall T1 T2 Gamma t1 t2,
  | T_Const : forall Gamma (n: nat),
  | T_Succ : forall Gamma t,
  | T_Pred : forall Gamma t,
  | T_Mult : forall t1 t2 Gamma,
  | T_If : forall t1 t2 t3 T1 Gamma,
*)
Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  remember empty as e eqn:Eg.
  intros t T Ht.
  induction Ht; subst.
  - (*var*) discriminate H.
  - (*abs*) left. constructor.
  - (*app*) right. 
    destruct IHHt1 as [Hv1 | [t1' Ht1']]; try reflexivity.
    + destruct IHHt2 as [Hv2 | [t2' Ht2']]; try reflexivity.
      * inversion Ht1; subst; try (inversion Hv1); subst. eexists. apply ST_AppAbs. assumption.
      * exists <{ t1 t2' }>. constructor. assumption. assumption.
    + exists <{ t1' t2 }>. constructor. assumption.
  - (*const*) left. constructor.
  - (*succ*) destruct IHHt as [Hv | [t' Ht']]; try reflexivity.
    + inversion Hv; subst; (try inversion Ht); subst.
      right. exists (S x0). constructor.
    + right. exists (<{ succ t' }>). constructor. assumption.
  - (*pred*) destruct IHHt as [Hv | [t' Ht']]; try reflexivity.
    + inversion Hv; subst; (try inversion Ht); subst.
      right. destruct x0; eauto.
    + right. exists (<{ pred t' }>). constructor. assumption.
  - (*mul*) right. 
    destruct IHHt1 as [Hv1 | [t1' Ht1']]; try reflexivity.
    + destruct IHHt2 as [Hv2 | [t2' Ht2']]; try reflexivity.
      * inversion Ht1; subst; try (inversion Hv1); subst. 
        inversion Ht2; subst; try (inversion Hv2); subst.
        exists (tm_const (n * n0)). apply ST_MulConst.
      * exists <{ t1 * t2' }>. constructor. assumption. assumption.
    + exists <{ t1' * t2 }>. constructor. assumption.
  - (*if*) right. destruct IHHt1 as [Hv1 | [t1' Ht1']]; try reflexivity. 
    + inversion Ht1; subst; try (inversion Hv1); subst.
      destruct n.
      * exists t2. constructor.
      * exists t3. constructor. auto.
    + exists <{ if0 t1' then t2 else t3 }>.
      constructor.
      assumption.
Qed.

End STLCArith.

