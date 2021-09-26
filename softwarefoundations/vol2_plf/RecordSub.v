Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Module RecordSub.

Inductive ty : Type :=
  (* proper types *)
  | Ty_Top : ty
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  (* record types *)
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.

Inductive tm : Type :=
  (* proper terms *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_rproj : tm -> string -> tm
  (* record terms *)
  | tm_rnil : tm
  | tm_rcons : string -> tm -> tm -> tm.

Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" := (tm_abs x t y) (in custom stlc at level 90, x at level 99,
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
Notation "'Top'" := (Ty_Top) (in custom stlc_ty at level 0).


Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.

Inductive well_formed_ty : ty -> Prop :=
  | wfTop :
        well_formed_ty <{{ Top }}>
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
Hint Constructors record_ty record_tm well_formed_ty : core.


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

Fixpoint Tlookup (i: string) (Tr: ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if eqb_string i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr' }> =>
      if eqb_string i i' then Some t else tlookup i tr'
  | _ => None
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
Hint Constructors step : core.


Reserved Notation "T '<:' U" (at level 40).
Inductive subtype : ty -> ty -> Prop :=
  (* Subtyping between proper types *)
  | S_Refl : forall T,
    well_formed_ty T ->
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    well_formed_ty S ->
    S <: <{{ Top }}>
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    <{{ S1 -> S2 }}> <: <{{ T1 -> T2 }}>
  (* Subtyping between record types *)
  | S_RcdWidth : forall i T1 T2,
    well_formed_ty <{{ i : T1 :: T2 }}> ->
    <{{ i : T1 :: T2 }}> <: <{{ nil }}>
  | S_RcdDepth : forall i S1 T1 Sr2 Tr2,
    S1 <: T1 ->
    Sr2 <: Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    <{{ i : S1 :: Sr2 }}> <: <{{ i : T1 :: Tr2 }}>
  | S_RcdPerm : forall i1 i2 T1 T2 Tr3,
    well_formed_ty <{{ i1 : T1 :: i2 : T2 :: Tr3 }}> ->
    i1 <> i2 ->
    <{{ i1 : T1 :: i2 : T2 :: Tr3 }}> <: <{{ i2 : T2 :: i1 : T1 :: Tr3 }}>
where "T '<:' U" := (subtype T U).
Hint Constructors subtype : core.



Module Examples.
Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation j := "j".
Notation k := "k".
Notation i := "i".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation C := <{{ Base "C" }}>.

Definition TRcd_j :=
  <{{ j : (B -> B) :: nil }}>. (* { j:B->B } *)

Definition TRcd_kj :=
  <{{ k : (A -> A) :: TRcd_j }}>. (* { k:C->C, j:B->B } *)

Example subtyping_example_0 :
  <{{ C -> TRcd_kj }}> <: <{{ C -> nil }}>.
Proof.
  apply S_Arrow.
    apply S_Refl. auto.
    unfold TRcd_kj, TRcd_j. apply S_RcdWidth; auto.
Qed.

Example subtyping_example_1 :
  TRcd_kj <: TRcd_j.  (* {k:A->A,j:B->B} <: {j:B->B} *)
Proof with eauto.
  unfold TRcd_kj, TRcd_j.
  eapply S_Trans.
  - apply S_RcdPerm...
    intro C. discriminate C.
  - apply S_RcdDepth...
Qed.

Example subtyping_example_2 :
  <{{ Top -> TRcd_kj }}> <: <{{ (C -> C) -> TRcd_j }}>.
Proof with eauto.
  apply S_Arrow.
  - apply S_Top...
  - apply subtyping_example_1.
Qed.

Example subtyping_example_3 :
  <{{ nil -> (j : A :: nil) }}> <: <{{ (k : B :: nil) -> nil }}>. (* {}->{j:A} <: {k:B}->{} *)
Proof with eauto.
  apply S_Arrow.
  - apply S_RcdWidth...
  - apply S_RcdWidth...
Qed.

Example subtyping_example_4 :
  <{{ x : A :: y : B :: z : C :: nil }}> <:
  <{{ z : C :: y : B :: x : A :: nil }}>.
Proof with eauto.
  apply S_Trans with (<{{ "y" : B :: "x" : A :: "z" : C :: nil }}>).
  - apply S_RcdPerm...
    intro C. discriminate C.
  - apply S_Trans with (<{{ "y" : B :: "z" : C :: "x" : A :: nil }}>).
    + apply S_RcdDepth...
      apply S_RcdPerm...
      intro C. discriminate C.
    + apply S_RcdPerm...
      intro C. discriminate C.
Qed.

End Examples.


Lemma subtype__wf : forall S T,
  S <: T ->
  well_formed_ty T /\ well_formed_ty S.
Proof with eauto.
  intros S T Hsub.
  induction Hsub;
    intros; try (destruct IHHsub1; destruct IHHsub2)...
  - (* S_RcdPerm *)
    split... inversion H. subst. inversion H5... Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  - (* RCons *)
    inversion H. subst. unfold Tlookup in H0.
    destruct (eqb_string i s)... inversion H0; subst... Qed.

Lemma rcd_types_match : forall S T i Ti,
  S <: T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ Si <: Ti.
Proof with (eauto using wf_rcd_lookup).
  intros S T i Ti Hsub Hget. generalize dependent Ti.
  induction Hsub; intros Ti Hget;
    try solve_by_invert.
  - (* S_Refl *)
    exists Ti...
  - (* S_Trans *)
    destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.
    destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.
    exists Si...
  - (* S_RcdDepth *)
    rename i0 into k.
    unfold Tlookup. unfold Tlookup in Hget.
    destruct (eqb_string i k)...
    + (* i = k -- we're looking up the first field *)
      inversion Hget. subst. exists S1...
  - (* S_RcdPerm *)
    exists Ti. split.
    + (* lookup *)
      unfold Tlookup. unfold Tlookup in Hget.
      destruct (eqb_stringP i i1)...
      * (* i = i1 -- we're looking up the first field *)
        destruct (eqb_stringP i i2)...
        (* i = i2 -- contradictory *)
        destruct H0.
        subst...
    + (* subtype *)
      inversion H. subst. inversion H5. subst... Qed.



Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{{ V1 -> V2 }}> ->
     exists U1 U2,
       (U = <{{ U1 -> U2 }}> ) /\ (V1 <: U1) /\ (U2 <: V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{{ V1 -> V2 }}> as V.
  generalize dependent V2. 
  generalize dependent V1.
  induction Hs; intros V1 V2 Hv; subst.
  - exists V1, V2. 
    inversion H...
  - destruct (IHHs2 V1 V2) as [U1 [U2 [Eu [Hv3u1 Hu2v4]]]]...
    destruct (IHHs1 U1 U2) as [U1' [U2' [Eu' [Hv3u1' Hu2v4']]]]...
    exists U1', U2'...
  - discriminate Hv.
  - injection Hv as Hv1 Hv2. subst.
    exists S1, S2...
  - discriminate Hv.
  - discriminate Hv.
  - discriminate Hv.
Qed.



Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc at level 99, T custom stlc_ty at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma (x : string) T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |- t12 \in T12 ->
      Gamma |- (\ x : T11, t12) \in (T11 -> T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T1 -> T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- t1 t2 \in T2
  | T_Proj : forall Gamma i t T Ti,
      Gamma |- t \in T ->
      Tlookup i T = Some Ti ->
      Gamma |- t --> i \in Ti
  (* Subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      subtype S T ->
      Gamma |- t \in T
  (* Rules for record terms *)
  | T_RNil : forall Gamma,
      Gamma |- nil \in nil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- i := t :: tr \in (i : T :: Tr)
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.


Module Examples2.
Import Examples.

Definition trcd_kj :=  <{ k := (\z : A, z) :: j := (\z : B, z) :: nil }>.

Example typing_example_0 :
  empty |- trcd_kj \in TRcd_kj.  (* empty ⊢ {k=(\z:A.z), j=(\z:B.z)} : {k:A->A,j:B->B} *)
Proof. unfold trcd_kj, TRcd_kj, TRcd_j.
  apply T_RCons.
  - apply T_Abs. auto. apply T_Var. auto. auto.
  - apply T_RCons.
    + apply T_Abs. auto. apply T_Var. auto. auto.
    + apply T_RNil.
    + auto.
    + auto.
  - auto.
  - auto.
Qed.

Example typing_example_1 :
  empty |- (\x : TRcd_j, x --> j) trcd_kj \in (B -> B).
(* empty ⊢ (\x:{k:A->A,j:B->B}. x.j) {k=(\z:A.z), j=(\z:B.z)} : B->B *)
Proof. unfold trcd_kj, TRcd_kj, TRcd_j.
  eapply T_App.
  - apply T_Abs. auto. apply T_Proj with (<{{ "j" : B -> B :: nil }}>). apply T_Var. auto.
    auto.
    auto.
  - apply T_Sub with TRcd_kj; unfold TRcd_kj, TRcd_j.
    + apply T_RCons. 
        apply T_Abs; auto. apply T_RCons. auto. auto. auto. auto. auto. auto.
    + eapply S_Trans. apply S_RcdPerm. auto.
      intro C. discriminate C.
      apply S_RcdDepth.
        auto.
        auto.
        auto.
        auto.
Qed.

Example typing_example_2 :
  empty |- (\ z : (C -> C) -> TRcd_j, (z (\ x : C, x) ) --> j )
            ( \z : (C -> C), trcd_kj ) \in (B -> B).
(* empty ⊢ (\z:(C->C)->{j:B->B}. (z (\x:C.x)).j)
              (\z:C->C. {k=(\z:A.z), j=(\z:B.z)})  : B->B *)
Proof.
  eapply T_App.
  - apply T_Abs. unfold TRcd_j. auto.
    eapply T_Proj. apply T_App with (<{{ C -> C }}>).
      apply T_Var. apply update_eq. unfold TRcd_j. auto.
    apply T_Abs. auto. auto.
    unfold TRcd_j. auto.
  - apply T_Sub with <{{ (C -> C) -> TRcd_kj }}>.
    + unfold trcd_kj, TRcd_kj, TRcd_j.
      apply T_Abs. auto.
      apply T_RCons. auto. 
      apply T_RCons. auto. 
      auto.
      auto.
      auto.
      auto.
      auto.
    + unfold TRcd_kj, TRcd_j. apply S_Arrow.
      * auto.
      * eapply S_Trans. apply S_RcdPerm. auto.
        intro C. discriminate C.
        apply S_RcdDepth. auto. auto. auto. auto.
Qed.
End Examples2.


Lemma has_type__wf : forall Gamma t T,
  has_type Gamma t T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  - (* T_App *)
    inversion IHHtyp1...
  - (* T_Proj *)
    eapply wf_rcd_lookup...
  - (* T_Sub *)
    apply subtype__wf in H.
    destruct H...
Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; eauto.
Qed.

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists vi, tlookup i v = Some vi /\ empty |- vi \in Ti.
Proof with eauto.
  remember empty as Gamma.
  intros t T i Ti Hval Htyp. generalize dependent Ti.
  induction Htyp; intros; subst; try solve_by_invert.
  - (* T_Sub *)
    apply (rcd_types_match S) in H0...
    destruct H0 as [Si [HgetSi Hsub]].
    eapply IHHtyp in HgetSi...
    destruct HgetSi as [vi [Hget Htyvi]]...
  - (* T_RCons *)
    simpl in H0. simpl. simpl in H1.
    destruct (eqb_string i i0).
    + (* i is first *)
      injection H1 as H1. subst. exists t...
    + (* i in tail *)
      eapply IHHtyp2 in H1...
      inversion Hval... Qed.


Lemma func_inher: forall S T1 T2,  
  S <: <{{ T1 -> T2 }}> -> exists U1 U2, S = <{{ U1 -> U2 }}> /\ T1 <: U1 /\ U2 <: T2.
Proof with eauto.
  intros S T1 T2 H.
  remember <{{ T1 -> T2 }}> as arr eqn:Earr.
  generalize dependent T1.
  generalize dependent T2.
  induction H; intros T2' T1' Ht.
  - subst. exists T1', T2'. split... inversion H...
  - subst. 
    destruct (IHsubtype2 T2' T1') as [U1 [U2 [Eu [T1Sub T2Sub]]]]...
    destruct (IHsubtype1 U2 U1 Eu) as [U1' [U2' [Eu' [T1Sub' T2Sub']]]]...
    exists U1', U2'...
  - discriminate Ht.
  - injection Ht as Ht1 Ht2; subst.
    exists S1, S2...
  - discriminate Ht.
  - discriminate Ht.
  - discriminate Ht.
Qed.


Lemma nil_not_fun: forall G T1 T2, ~ (G |- nil \in (T1 -> T2)).
Proof.
  intros G T1 T2 Hnil.
  remember <{{ (T1 -> T2) }}> as fty eqn:Efty.
  remember <{ nil }> as n eqn:En.
  generalize dependent T1.
  generalize dependent T2.
  induction Hnil; intros T2' T1' HT; subst;
    try (discriminate En).
  - inversion H; subst.
    + eapply (IHHnil). reflexivity. reflexivity.
    + apply func_inher in H.
      destruct H as [U1 [U2 [Eu [T1Sub T2Sub]]]].
      eapply IHHnil. reflexivity.
      apply Eu.
    + eapply IHHnil. reflexivity.
      reflexivity.
  - discriminate HT.
Qed.

Lemma rec_not_fun: forall i v1 vr G T1 T2, ~(G |- i := v1 :: vr \in (T1 -> T2)).
Proof.
  intros i v1 vr G T1 T2 Hnil.
  remember <{{ (T1 -> T2) }}> as fty eqn:Efty.
  remember <{ i := v1 :: vr }> as n eqn:En.
  generalize dependent T1.
  generalize dependent T2.
  induction Hnil; intros T2' T1' HT; subst;
    try (discriminate En).
  - inversion H; subst.
    + eapply (IHHnil). reflexivity. reflexivity.
    + apply func_inher in H.
      destruct H as [U1 [U2 [Eu [T1Sub T2Sub]]]].
      eapply IHHnil. reflexivity.
      apply Eu.
    + eapply IHHnil. reflexivity.
      reflexivity.
  - discriminate HT.
Qed.

(*  G |- i := v1 :: vr \in (T1 -> T2)  *)

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
     Gamma |- s \in (T1 -> T2) ->
     value s ->
     exists x S1 s2, s = <{ \ x : S1, s2 }>.
Proof with eauto.
  intros G s T1 T2 Ht Hv.
  inversion Hv; subst.
  - exists x, T0, t1...
  - exfalso. apply (nil_not_fun _ _ _ Ht).
  - exfalso. apply (rec_not_fun i v1 vr G T1 T2 Ht).
Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  - (* T_Var *)
    inversion H.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists <{ [x:=t2] t12 }>...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }> ...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_Proj *)
    right. destruct IHHt...
    + (* rcd is value *)
      destruct (lookup_field_in_value t T i Ti)
        as [t' [Hget Ht']]...
    + (* rcd_steps *)
      destruct H0 as [t' Hstp]. exists <{ t' --> i }>...
  - (* T_RCons *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2...
      * (* tail steps *)
        right. destruct H2 as [tr' Hstp].
        exists <{ i := t :: tr' }>...
    + (* head steps *)
      right. destruct H1 as [t' Hstp].
      exists <{ i := t' :: tr}>... Qed.



Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- \ x : S1, t2 \in T ->
     (exists S2, <{{ S1 -> S2 }}> <: T  /\  (x |-> S1; Gamma) |- t2 \in S2).
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{ \ x : S1, t2 }> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    assert (Hwf := has_type__wf _ _ _ H0).
    exists T12...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- \x : S1, s2 \in (T1 -> T2) ->
     T1 <: S1  /\  (x |-> S1) |- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst... Qed.




Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T ->
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
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - (* T_Var *)
    rename x0 into y.
    destruct (eqb_stringP x y) as [Hxy|Hxy]; subst.
    + (* x = y *)
      rewrite update_eq in H.
      injection H as H. subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var; [|assumption].
      rewrite update_neq in H; assumption.
  - (* T_Abs *)
    rename x0 into y. subst.
    destruct (eqb_stringP x y) as [Hxy|Hxy]; apply T_Abs; try assumption.
    + (* x=y *)
      subst. rewrite update_shadow in Ht. assumption.
    + (* x <> y *)
      subst. apply IHHt.
      rewrite update_permute; auto.
      - (* rcons *) (* <=== only new case compared to pure STLC *)
      apply T_RCons; eauto.
      inversion H0; subst; simpl; auto.
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
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0...
  - (* T_Proj *)
    inversion HE; subst...
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Hty]].
    rewrite H4 in Hget. inversion Hget. subst...
  - (* T_RCons *)
    inversion HE; subst...
    eauto using step_preserves_record_tm. Qed.

End RecordSub.
