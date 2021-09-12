Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.

Hint Constructors multi : core.

Inductive qwe (n: nat): nat -> Prop :=
  | asd : qwe n 1
  | zxc (j k : nat): nat -> qwe n 2
.

Definition foo (q: nat) (qq: qwe 1 q) : (qwe q 1) :=
  match qq in (qwe _ b) with
  | asd _ => asd q
  | zxc _ j k nn => asd q
  end.

Definition zxc_mk: qwe 111 2 := zxc 111 2 999 888.








Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc (t: tm) (H: nvalue t) : nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.
Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.





Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall v,
      nvalue v ->
      (prd (scc v)) --> v
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall v,
       nvalue v ->
      (iszro (scc v)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')
where "t '-->' t'" := (step t t').
Hint Constructors step : core.



Notation step_normal_form := (normal_form step).
Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~(value t).
Hint Unfold stuck : core.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (scc tru).
  split.
  - intros [t' H].
    inversion H.
    inversion H1.
  - intros H.
    inversion H; inversion H0.
    inversion H2.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t.
  induction t; intros Hval [t' H].
  - inversion H.
  - inversion H.
  - inversion Hval; inversion H0.
  - inversion H.
  - inversion Hval.
    + inversion H0.
    + inversion H0; subst. inversion H. 
      apply IHt.
      assert (G: value t). { right. apply H2. }
      apply G. 
      eexists. apply H3.
  - inversion Hval.
    + inversion H0.
    + inversion H0.
  - inversion Hval.
    + inversion H0.
    + inversion H0.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  intros t.
  induction t; intros y1 y2 H1 H2.
  - inversion H1.
  - inversion H1.
  - inversion H1; subst. 
    + inversion H2; subst. reflexivity. inversion H5.
    + inversion H2; subst. reflexivity. inversion H5.
    + inversion H2; subst. inversion H5. inversion H5.
      assert (G: t1' = t1'0). { apply IHt1. auto. auto. }
      rewrite -> G.
      reflexivity.
  - inversion H1.
  - inversion H1; subst. inversion H2; subst. 
    assert (G: t1' = t1'0). { apply IHt. auto. auto. }
    rewrite G. reflexivity.
  - inversion H1; subst. 
    + (* zero *) inversion H2; subst. reflexivity.
      inversion H0.
    + (* succ *) inversion H2; subst. reflexivity.
      inversion H2. inversion H4.
      exfalso.
      apply value_is_nf with (scc y1).
        right. constructor. assumption.
        eexists. apply H3.
    + (* step *)
      inversion H2; subst.
      * inversion H1. inversion H0.
      * exfalso.
        apply value_is_nf with (scc y2).
          right. constructor. assumption.
          eexists. apply H0.
      * assert (G: t1' = t1'0). { apply IHt. assumption. assumption. }
        rewrite G. reflexivity.
  - inversion H1; subst.
    + inversion H2; subst. reflexivity. inversion H0.
    + inversion H2; subst. reflexivity.
      exfalso.
      apply value_is_nf with (scc v).
        right. constructor. assumption.
        eexists. apply H3.
    + inversion H2; subst. 
      * inversion H0.
      * exfalso.
        apply value_is_nf with (scc v).
          right. constructor. assumption.
          eexists. apply H0.
      * assert (G: t1' = t1'0). { apply IHt. assumption. assumption. }
        rewrite G.
        reflexivity.
Qed.



Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).
Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool
where "'|-' t '\in' T" := (has_type t T).
Hint Constructors has_type : core.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
  - apply T_Fls.
  - apply T_Zro.
  - apply T_Scc. apply T_Zro.
Qed.

Example has_type_not :
  ~( |- test fls zro tru \in Bool ).
Proof.
  intros HContra. inversion HContra.
  inversion H4.
Qed.

Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t \in Nat ->
  |- t \in Nat.
Proof. intros t H.
  inversion H.
  assumption.
Qed.


Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT.
  - left. constructor. constructor.
  - left. constructor. constructor.
  - inversion IHHT1 as [Ht1val | [t1' Ht1prorg]].
    + inversion Ht1val.
      * inversion H; subst.
        -- (*true*) right. exists t2. constructor.
        -- (*false*) right. exists t3. constructor.
      * (*num*) inversion H; subst. inversion HT1. inversion HT1.
    + right. exists (test t1' t2 t3). constructor. assumption.
  - left. right. apply nv_zro.
  - destruct IHHT as [Hv | [t1' Hp]].
    + left. right. apply nv_scc.
      apply nat_canonical.
      apply HT.
      apply Hv.
    + right. exists (scc t1'). constructor. apply Hp.
  - right.
    inversion IHHT.
    + destruct (nat_canonical _ HT H).
      * exists zro. constructor.
      * exists t. constructor. apply n.
    + destruct H as [t' H].
      exists (prd t'). constructor. apply H.
  - right.
    inversion IHHT.
    + destruct (nat_canonical _ HT H).
      * exists tru. constructor.
      * exists fls. constructor. apply n.
    + destruct H as [t' H].
      exists (iszro t'). constructor. apply H.
Qed.


Lemma nval_Nat: forall t, nvalue t -> |- t \in Nat.
Proof.
  intros t H.
  induction H.
  - constructor.
  - constructor. assumption.
Qed.

Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         intros t' HE;
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    - (* scc *) inversion HE; subst; clear HE.
      constructor. apply IHHT. assumption.
    - inversion HE; subst; clear HE.
      + constructor.
      + apply (nval_Nat _ H0).
      + constructor. apply IHHT. assumption.
    - inversion HE; subst; clear HE; try constructor.
      apply IHHT. assumption.
Qed.

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof with eauto.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT.
  - inversion HT. assumption.
  - inversion HT. assumption.
  - inversion HT; subst. constructor.
    + apply IHHE. assumption.
    + assumption.
    + assumption.
  - inversion HT; subst. constructor.
    apply IHHE. assumption.
  - inversion HT; subst. constructor.
  - inversion HT; subst. inversion H1. assumption.
  - inversion HT; subst. constructor. apply IHHE. assumption.
  - inversion HT; subst. constructor.
  - inversion HT; subst. constructor.
  - inversion HT; subst. constructor. apply IHHE. assumption.
Qed.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.


Theorem reverse_preservation : forall t',
  |- t' \in Bool ->
  exists t, (t --> t'  /\  ~(|- t \in Bool)).
Proof.
  intros t' HT.

  exists (test tru t' zro).
  split.
  - constructor.
  - intro H.
    inversion H; subst.
    inversion H6. 
Qed.


(* TODO Ex *)