Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

Module STLCExtendedRecords.

Module FirstTry.
  Definition alist (X : Type) := list (string * X).
  Inductive ty : Type :=
    | Base : string -> ty
    | Arrow : ty -> ty -> ty
    | TRcd : (alist ty) -> ty.

  Check ty_ind.
  (*  ====>
      ty_ind :
        forall P : ty -> Prop,
          (forall i : id, P (Base i)) ->
          (forall t : ty, P t -> forall t0 : ty, P t0
                              -> P (Arrow t t0)) ->
          (forall a : alist ty, P (TRcd a)) ->    (* ??? *)
          forall t : ty, P t
  *)
End FirstTry.



Inductive ty : Type :=
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.


Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* records *)
  | tm_rproj : tm -> string -> tm
  | tm_rnil : tm
  | tm_rcons : string -> tm -> tm -> tm.

Declare Custom Entry stlc_ty.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
Notation "{ x }" := x (in custom stlc at level 1, x constr).
Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0).
Notation " l ':' t1 '::' t2" := (Ty_RCons l t1 t2) (in custom stlc_ty at level 3, right associativity).
Notation " l := e1 '::' e2" := (tm_rcons l e1 e2) (in custom stlc at level 3, right associativity).
Notation "'nil'" := (Ty_RNil) (in custom stlc_ty).
Notation "'nil'" := (tm_rnil) (in custom stlc).
Notation "o --> l" := (tm_rproj o l) (in custom stlc at level 0).

Open Scope string_scope.
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".

Definition weird_type := <{{ a : A :: B }}>.

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.

Inductive well_formed_ty : ty -> Prop :=
  | wfBase : forall (i : string),
        well_formed_ty <{{ Base i }}>
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty <{{ T1 -> T2 }}>
  | wfRNil :
        well_formed_ty <{{ nil }}>
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty <{{ i : T1 :: T2 }}>.
Hint Constructors record_ty well_formed_ty : core.



Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.
Hint Constructors record_tm : core.



Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{ t1 --> i }> =>
      <{ ( [x := s] t1) --> i }>
  | <{ nil }> =>
      <{ nil }>
  | <{ i := t1 :: tr }> =>
     <{ i := [x := s] t1 :: ( [x := s] tr) }>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).



Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{ \ x : T2, t1 }>
  | v_rnil : value <{ nil }>
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value <{ i := v1 :: vr }>.
Hint Constructors value : core.


Fixpoint tlookup (i: string) (tr: tm) : option tm :=
  match tr with
  | <{ i' := t :: tr'}> => if eqb_string i i' then Some t else tlookup i tr'
  | _                   => None
  end.


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
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        <{ t1 --> i }> --> <{ t1' --> i }>
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        <{ tr --> i }> --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        <{ i := t1 :: tr2 }> --> <{ i := t1' :: tr2 }>
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        <{ i := v1 :: tr2 }> --> <{ i := v1 :: tr2' }>
where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors step : core.



Fixpoint Tlookup (i: string) (Tr: ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if eqb_string i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).
Inductive has_type (Gamma : context) :tm -> ty -> Prop :=
  | T_Var : forall x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- x \in T
  | T_Abs : forall x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |- t12 \in T12 ->
      Gamma |- \x : T11, t12 \in (T11 -> T12)
  | T_App : forall T1 T2 t1 t2,
      Gamma |- t1 \in (T1 -> T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- ( t1 t2) \in T2
  (* records: *)
  | T_Proj : forall i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (t --> i) \in Ti
  | T_RNil :
      Gamma |- nil \in nil
  | T_RCons : forall i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- ( i := t :: tr) \in ( i : T :: Tr)
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.



Lemma typing_example_2 :
  empty |- (\a : ( i1 : (A -> A) :: i2 : (B -> B) :: nil), a --> i2)
            ( i1 := (\a : A, a) :: i2 := (\a : B,a ) :: nil ) \in (B -> B).
Proof.
  eapply T_App.
  - (* abs *)
    apply T_Abs.
    + apply wfRCons.
        constructor. constructor. constructor.
        apply wfRCons. 
          constructor. constructor. constructor.
          constructor.
          constructor.
      apply RTcons.
    + eapply T_Proj.
      apply T_Var. apply update_eq.
        constructor. constructor. constructor. constructor.
        constructor. constructor. constructor. constructor.
        constructor. constructor. constructor. 
      simpl. reflexivity.
  - (* val *)
    auto.
Qed.


Example typing_nonexample :
  ~ exists T,
     (g |-> <{{ i2 : (A -> A) :: nil }}>)  |-  ( i1 := (\a : B, a) :: g ) \in T.
Proof.
  intros [T HContra].
  inversion HContra; subst.
  inversion H6.
Qed.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (y |-> A) |- (\a : ( i1 : A :: nil ), a --> i1 ) ( i1 := y :: i2 := y :: nil ) \in T.
Proof.
  intros y [T HContra].
  inversion HContra; subst.
  inversion H3; subst.
  inversion H1; subst.
  inversion H5; subst.
Qed.


Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  - (* RCons *)
    inversion H. subst. unfold Tlookup in H0.
    destruct (eqb_string i s)...
    inversion H0. subst... Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  - (* T_App *)
    inversion IHHtyp1...
  - (* T_Proj *)
    eapply wf_rcd_lookup...
Qed.

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember empty as Gamma.
  induction Htyp; subst; try solve_by_invert...
  - (* T_RCons *)
    simpl in Hget. simpl. destruct (eqb_string i i0).
    + (* i is first *)
      simpl. injection Hget as Hget. subst.
      exists t...
    + (* get tail *)
      destruct IHHtyp2 as [vi [Hgeti Htypi] ]...
      inversion Hval... Qed.


Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  (* Theorem: Suppose empty ⊢ t : T.  Then either
       1. t is a value, or
       2. t --> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be
       T_Var, since it can never be the case that
       empty ⊢ x : T (since the context is empty). *)
    inversion H.
  - (* T_Abs *)
    (* If the T_Abs rule was the last used, then
       t = abs x T11 t12, which is a value. *)
    left...
  - (* T_App *)
    (* If the last rule applied was T_App, then t = t1 t2,
       and we know from the form of the rule that
         empty ⊢ t1 : T1 → T2
         empty ⊢ t2 : T1
       By the induction hypothesis, each of t1 and t2 either is a value
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
      (* If both t1 and t2 are values, then we know that
         t1 = abs x T11 t12, since abstractions are the only
         values that can have an arrow type.  But
         (abs x T11 t12) t2 --> [x:=t2]t12 by ST_AppAbs. *)
        inversion H; subst; try solve_by_invert.
        exists <{ [x:=t2]t0 }>...
      * (* t2 steps *)
        (* If t1 is a value and t2 --> t2', then
           t1 t2 --> t1 t2' by ST_App2. *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      (* Finally, If t1 --> t1', then t1 t2 --> t1' t2
         by ST_App1. *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_Proj *)
    (* If the last rule in the given derivation is T_Proj, then
       t = rproj t i and
           empty ⊢ t : (TRcd Tr)
       By the IH, t either is a value or takes a step. *)
    right. destruct IHHt...
    + (* rcd is value *)
      (* If t is a value, then we may use lemma
         lookup_field_in_value to show tlookup i t = Some ti
         for some ti which gives us rproj i t --> ti by
         ST_ProjRcd. *)
      destruct (lookup_field_in_value _ _ _ _ H0 Ht H)
        as [ti [Hlkup _] ].
      exists ti...
    + (* rcd_steps *)
      (* On the other hand, if t --> t', then
         rproj t i --> rproj t' i by ST_Proj1. *)
      destruct H0 as [t' Hstp]. exists <{ t' --> i }>...
  - (* T_RNil *)
    (* If the last rule in the given derivation is T_RNil,
       then t = trnil, which is a value. *)
    left...
  - (* T_RCons *)
    (* If the last rule is T_RCons, then t = rcons i t tr and
         empty ⊢ t : T
         empty ⊢ tr : Tr
       By the IH, each of t and tr either is a value or can
       take a step. *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2; try reflexivity.
      * (* tail is a value *)
      (* If t and tr are both values, then rcons i t tr
         is a value as well. *)
        left...
      * (* tail steps *)
        (* If t is a value and tr --> tr', then
           rcons i t tr --> rcons i t tr' by
           ST_Rcd_Tail. *)
        right. destruct H2 as [tr' Hstp].
        exists <{ i := t :: tr'}>...
    + (* head steps *)
      (* If t --> t', then
         rcons i t tr --> rcons i t' tr
         by ST_Rcd_Head. *)
      right. destruct H1 as [t' Hstp].
      exists <{ i := t' :: tr }>... Qed.


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
  (x |-> U ; Gamma) |- t \in T ->
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
      rewrite update_eq in H1.
      injection H1 as H1; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H1; auto. assumption.
  - (* abs *)
    rename s into y, t into T.
    destruct (eqb_stringP x y); subst; apply T_Abs; try assumption.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
  - (* rcons *) (* <=== only new case compared to pure STLC *)
     apply T_RCons; eauto.
     inversion H7; subst; simpl; auto.
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
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  - (* T_Proj *) (* <=== new case compared to pure STLC *)
    (* If the last rule was T_Proj, then t = rproj t1 i.
       Two rules could have caused t --> t': T_Proj1 and
       T_ProjRcd.  The typing of t' follows from the IH
       in the former case, so we only consider T_ProjRcd.

       Here we have that t is a record value.  Since rule
       T_Proj was used, we know empty ⊢ t \in Tr and
       Tlookup i Tr = Some Ti for some i and Tr.
       We may therefore apply lemma lookup_field_in_value
       to find the record element this projection steps to. *)
    inversion HE; subst...
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Htyp] ].
    rewrite H4 in Hget. injection Hget as Hget. subst...
  - (* T_RCons *) (* <=== new case compared to pure STLC *)
    (* If the last rule was T_RCons, then t = rcons i t tr
       for some i, t and tr such that record_tm tr.  If
       the step is by ST_Rcd_Head, the result is immediate by
       the IH.  If the step is by ST_Rcd_Tail, tr --> tr2'
       for some tr2' and we must also use lemma step_preserves_record_tm
       to show record_tm tr2'. *)
    inversion HE; subst...
    apply T_RCons... eapply step_preserves_record_tm...
Qed.

End STLCExtendedRecords.
