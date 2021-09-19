Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.

Inductive ty : Type :=
  | Ty_Top : ty
  | Ty_Bool : ty
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).
Notation "'Base' x" := (Ty_Base x) (in custom stlc at level 0).
Notation "'Top'" := (Ty_Top) (in custom stlc at level 0).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).


Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> =>
      <{unit}>
  | <{ ( l , r ) }> => <{ ( [x:=s]l , [x:=s]r ) }>
  | <{ t.fst }> => <{ ([x:=s]t).fst }>
  | <{ t.snd }> => <{ ([x:=s]t).snd }>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.
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
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Pair1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{ (t1 , t2) }> --> <{ (t1' , t2) }>
  | ST_Pair2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{ (v1 , t2) }> --> <{ (v1 , t2') }>
  | ST_PairFstStep : forall t t',
       t --> t' ->
       <{ t.fst }> --> <{ t'.fst }>
  | ST_PairFst : forall v1 v2,
       <{ (v1 , v2).fst }> --> <{ v1 }>
  | ST_PairSndStep : forall t t',
       t --> t' ->
       <{ t.snd }> --> <{ t'.snd }>
  | ST_PairSnd : forall v1 v2,
       <{ (v1 , v2).snd }> --> <{ v2 }>
where "t '-->' t'" := (step t t').
Hint Constructors step : core.


Reserved Notation "T '<:' U" (at level 40).
Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Pair : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1 * S2}> <: <{T1 * T2}>
where "T '<:' U" := (subtype T U).


Hint Constructors subtype : core.
Module Examples.
Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation A := <{Base "A"}>.
Notation B := <{Base "B"}>.
Notation C := <{Base "C"}>.
Notation String := <{Base "String"}>.
Notation Float := <{Base "Float"}>.
Notation Integer := <{Base "Integer"}>.

Example subtyping_example_0 :
  <{C->Bool}> <: <{C->Top}>.
Proof. auto. Qed.

Definition Person : ty := <{ (String * Top)}>.

Definition Student : ty := <{ (String * Float)}>.

Definition Employee : ty := <{ (String * Integer)}>.

Example sub_student_person :  Student <: Person.
Proof. apply S_Pair. apply S_Refl. apply S_Top. Qed.

Example sub_employee_person :  Employee <: Person.
Proof. apply S_Pair. apply S_Refl. apply S_Top. Qed.

Example subtyping_example_1 :
  <{Top->Student}> <: <{(C->C)->Person}>.
Proof with eauto.
  apply S_Arrow...
  apply sub_student_person. Qed.


Example subtyping_example_2 :
  <{Top->Person}> <: <{Person->Top}>.
Proof with eauto.
  apply S_Arrow... Qed.

End Examples.



Definition context := partial_map ty.
Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before: *)
  (* pure STLC *)
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
  | T_True : forall Gamma,
       Gamma |- true \in Bool
  | T_False : forall Gamma,
       Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |- t1 \in T2
  (* Pair *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (t1 , t2) \in (T1 * T2)
  | T_PairFst : forall Gamma t T1 T2,
      Gamma |- t \in (T1 * T2) ->
      Gamma |- t.fst \in T1
  | T_PairSnd : forall Gamma t T1 T2,
      Gamma |- t \in (T1 * T2) ->
      Gamma |- t.snd \in T2
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Module Examples2.
Import Examples.


Example e21: forall A B, empty |- ((\z:A, z) , (\z:B, z)) \in ((A->A) * (B->B)).
Proof. intros A B. eapply (T_Pair empty <{ \z:A, z }> <{ \z:B, z }> <{ A->A }> <{ B->B }>).
  - apply T_Abs. apply T_Var. auto.
  - apply T_Abs. apply T_Var. auto.
Qed.

Example e22: forall A B, empty |- (\x:(Top * (B->B)), x.snd) ((\z:A, z), (\z:B, z)) \in (B -> B).
Proof. intros A B.
  eapply T_App.
  - apply T_Abs. eapply T_PairSnd. apply T_Var. unfold "|->". rewrite t_update_eq. reflexivity.
  - apply T_Pair.
    + apply T_Sub with <{ A -> A }>. (* Anything subtype of Top *)
      * apply T_Abs. apply T_Var. unfold "|->". rewrite t_update_eq. reflexivity.
      * apply S_Top.
    + apply T_Abs. apply T_Var. unfold "|->". rewrite t_update_eq. reflexivity.
Qed.

Example e23: forall A B C, empty |- (\z:(C->C)->(Top * (B->B)), (z (\x:C, x)).snd)
              (\z:C->C, ((\z:A, z), (\z:B, z)))
         \in (B->B).
Proof. intros A B C.
  apply T_App with <{ (C -> C) -> Top * (B -> B) }>.
  - apply T_Abs. eapply T_PairSnd. eapply T_App. 
    + apply T_Var. unfold "|->". rewrite t_update_eq. reflexivity.
    + apply T_Abs. apply T_Var. unfold "|->". rewrite t_update_eq. reflexivity.
  - apply T_Abs. apply T_Pair.
    + apply T_Sub with <{ A -> A }>. 
      * apply T_Abs. apply T_Var. unfold "|->". rewrite t_update_eq. reflexivity.
      * apply S_Top.
    + apply T_Abs. apply T_Var. unfold "|->". rewrite t_update_eq. reflexivity.
Qed.

End Examples2.


Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> -> U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs; subst; try auto; try (inversion HeqV).
  - rewrite -> IHHs1; apply IHHs2; reflexivity.
Qed.


Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{ V1 -> V2 }> ->
     exists U1 U2, U = <{ U1 -> U2 }> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{ V1 -> V2 }> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros V1 V2 Ev; subst; try (inversion Ev).
  - exists V1, V2. split; try reflexivity. split; apply S_Refl.
  - destruct (IHHs2 V1 V2) as [ U1 [ U2  [Eu [ Hv1s Hu2s] ] ] ]. reflexivity.
    subst.
    destruct (IHHs1 U1 U2) as [ U1' [ U2'  [Eu' [ Hv1s' Hu2s'] ] ] ]. reflexivity.
    subst.
    exists U1', U2'.
    split. reflexivity.
    split.
    + apply (S_Trans _ _ _ Hv1s Hv1s').
    + apply (S_Trans _ _ _ Hu2s' Hu2s).
  - exists S1, S2.
    split. reflexivity.
    split.
    + rewrite <- H0. assumption.
    + rewrite <- H1. assumption.
Qed.


Lemma bool_if_bottom_for_true: forall G T, G |- true \in T -> <{ Bool }> <: T.
Proof.
  intros G T H.
  remember <{ true }> as t eqn:Et.
  induction H; try (discriminate Et).
  - constructor.
  - subst. apply S_Trans with T1.
    + apply IHhas_type. reflexivity.
    + assumption.
Qed.

Lemma true_isnt_arrow: forall G T1 T2, ~(G |- true \in (T1 -> T2)).
Proof.
  intros G T1 T2 H.
  inversion H; subst.
  apply bool_if_bottom_for_true in H.
  apply sub_inversion_arrow in H.
  destruct H as [U1 [U2 [HT0 [HU1 HU2]]]]. 
  discriminate HT0.
Qed.


Lemma bool_if_bottom_for_false: forall G T, G |- false \in T -> <{ Bool }> <: T.
Proof.
  intros G T H.
  remember <{ false }> as t eqn:Et.
  induction H; try (discriminate Et).
  - constructor.
  - subst. apply S_Trans with T1.
    + apply IHhas_type. reflexivity.
    + assumption.
Qed.

Lemma false_isnt_arrow: forall G T1 T2, ~(G |- false \in (T1 -> T2)).
Proof.
  intros G T1 T2 H.
  inversion H; subst.
  apply bool_if_bottom_for_false in H.
  apply sub_inversion_arrow in H.
  destruct H as [U1 [U2 [HT0 [HU1 HU2]]]]. 
  discriminate HT0.
Qed.

Lemma unit_is_bottom_for_unit: forall G T, G |- unit \in T -> <{ Unit }> <: T.
Proof.
  intros G T H.
  remember <{ unit }> as t eqn:Et.
  induction H; try (discriminate Et).
  - constructor.
  - subst. apply S_Trans with T1.
    + apply IHhas_type. reflexivity.
    + assumption.
Qed.

Lemma unit_isnt_arrow: forall G T1 T2, ~(G |- unit \in (T1 -> T2)).
Proof.
  intros G T1 T2 H.
  inversion H; subst.
  apply unit_is_bottom_for_unit in H.
  apply sub_inversion_arrow in H.
  destruct H as [U1 [U2 [HT0 [HU1 HU2]]]]. 
  discriminate HT0.
Qed.


Lemma pair_is_bottom_for_pair: forall G v1 v2 T, G |- (v1, v2) \in T -> exists T1 T2, <{ T1 * T2 }> <: T.
Proof.
  intros G v1 v2 T H.
  remember <{ (v1, v2) }> as t eqn:Et.
  induction H; try (discriminate Et).
  - subst. 
    destruct IHhas_type as [T2' [T3' H']]. reflexivity.
    exists T2', T3'.
    apply S_Trans with T1.
    + apply H'.
    + assumption.
  - exists T1, T2. constructor.
Qed.

Lemma pair_isnt_arrow: forall G v1 v2 T1 T2, ~(G |- (v1, v2) \in (T1 -> T2)).
Proof.
  intros G v1 v2 T1 T2 H.
  inversion H; subst.
  apply pair_is_bottom_for_pair in H.
  destruct H as [T' [T'' H']].
  apply sub_inversion_arrow in H'.
  destruct H' as [U1 [U2 [HT0 [HU1 HU2]]]]. 
  discriminate HT0.
Qed.


Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in (T1 -> T2) ->
  value s ->
  exists x S1 s2, s = <{ \x:S1, s2 }>.
Proof with eauto.
  intros G s T1 T2 Ht Hv.
  generalize dependent G.
  generalize dependent T1.
  generalize dependent T2.
  induction Hv. 
  - intros T1 T2' G Ht. exists x, T2, t1. reflexivity.
  - intros T2 T1 G Ht. exfalso. apply (true_isnt_arrow G T1 T2 Ht).
  - intros T2 T1 G Ht. exfalso. apply (false_isnt_arrow G T1 T2 Ht).
  - intros T2 T1 G Ht. exfalso. apply (unit_isnt_arrow G T1 T2 Ht).
  - intros T2 T1 G Ht. exfalso. apply (pair_isnt_arrow G v1 v2 T1 T2 Ht).
Qed.


Lemma abs_is_bottom_for_abs: forall G x xT b T, G |- (\x:xT, b) \in T -> exists T1 T2, <{ T1 -> T2 }> <: T.
Proof.
  intros G x xT b T H.
  remember <{ (\x:xT, b) }> as f eqn:Ef.
  induction H; try (discriminate Ef).
  - subst.
    injection Ef as Ex Et Eb. subst.
    exists xT, T1. constructor.
  - subst.
    destruct IHhas_type as [T2' [T3' H']]. reflexivity.
    exists T2', T3'.
    apply S_Trans with T1.
    + apply H'.
    + assumption.
Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- (\x:S1, t2) \in T ->
     exists S2, <{ S1 -> S2 }> <: T  /\  (x |-> S1 ; Gamma) |- t2 \in S2.
Proof.
  intros G x S1 t2 T H.
  remember <{ (\x:S1, t2) }> as f eqn:Ef.
  induction H; try (discriminate Ef).
  - injection Ef as Ex Et Eb. subst.
    exists T1. split. 
      constructor.
      assumption.
  - subst.
    destruct IHhas_type as [T2' [T3' H']]. reflexivity.
    exists T2'.
    split.
    * apply S_Trans with T1; assumption.
    * assumption.
Qed.

Lemma sub_inversion_pair : forall U V1 V2,
     U <: <{ V1 * V2 }> ->
     exists U1 U2, U = <{ U1 * U2 }> /\ U1 <: V1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{ V1 * V2 }> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros V1 V2 Ev; subst; try (inversion Ev).
  - exists V1, V2. split; try reflexivity. split; apply S_Refl.
  - destruct (IHHs2 V1 V2) as [ U1 [ U2  [Eu [ Hv1s Hu2s] ] ] ]. reflexivity.
    subst.
    destruct (IHHs1 U1 U2) as [ U1' [ U2'  [Eu' [ Hv1s' Hu2s'] ] ] ]. reflexivity.
    subst.
    exists U1', U2'.
    split. reflexivity.
    split.
    + apply (S_Trans _ _ _ Hv1s' Hv1s).
    + apply (S_Trans _ _ _ Hu2s' Hu2s).
  - exists S1, S2.
    split. reflexivity.
    split.
    + rewrite <- H0. assumption.
    + rewrite <- H1. assumption.
Qed.


Lemma canonical_forms_of_pair_types : forall Gamma s T1 T2,
  Gamma |- s \in (T1 * T2) ->
  value s ->
  exists v1 v2, s = <{ (v1, v2) }>.
Proof with eauto.
  intros G s T1 T2 Ht Hv.
  generalize dependent G.
  generalize dependent T1.
  generalize dependent T2.
  induction Hv. 
  - intros T1 T' G Ht. exfalso.
    apply abs_is_bottom_for_abs in Ht.
    destruct Ht as [T2' [T3' Ht]].
    apply sub_inversion_pair in Ht.
    destruct Ht as [U1' [U2' [Ht [Hu1 Hu2]]]].
    discriminate Ht.
  - intros T2 T1 G Ht. exfalso.
    apply bool_if_bottom_for_true in Ht.
    apply sub_inversion_pair in Ht.
    destruct Ht as [U1' [U2' [Ht [Hu1 Hu2]]]].
    discriminate Ht.
  - intros T2 T1 G Ht. exfalso.
    apply bool_if_bottom_for_false in Ht.
    apply sub_inversion_pair in Ht.
    destruct Ht as [U1' [U2' [Ht [Hu1 Hu2]]]].
    discriminate Ht.
  - intros T2 T1 G Ht. exfalso.
    apply unit_is_bottom_for_unit in Ht.
    apply sub_inversion_pair in Ht.
    destruct Ht as [U1' [U2' [Ht [Hu1 Hu2]]]].
    discriminate Ht.
  - intros T2 T1 G Ht. exists v1, v2. reflexivity.
Qed.


Lemma abs_is_bottom_for_fun: forall G x T2 t1 T, G |- \ x : T2, t1 \in T -> exists T1, <{ T2 -> T1 }> <: T.
Proof.
  intros G x T2 t1 T H.
  remember <{ (\x : T2, t1) }> as t eqn:Et.
  induction H; try (discriminate Et).
  - injection Et as Et1 Et2 Et3. subst. exists T1. constructor.
  - subst. 
    destruct IHhas_type as [T3' H']. 
      reflexivity. 
    exists T3'. apply S_Trans with T1.
    + apply H'.
    + assumption.
Qed.

Lemma typing_inversion_var : forall Gamma (x:string) T,
  Gamma |- x \in T ->
  exists S, Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros G x T H.
  remember (tm_var x) as t eqn:Et.
  induction H; try (discriminate Et).
  - exists T1. split.
    + injection Et as Et. rewrite Et in H. assumption.
    + constructor.
  - destruct IHhas_type as [S' [Hl' Hr']]...
Qed.


Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |- t1 t2 \in T2 ->
  exists T1,  Gamma |- t1 \in (T1 -> T2) /\ Gamma |- t2 \in T1.
Proof with eauto.
  intros G t1 t2 T2 H.
  remember <{ t1 t2 }> as t eqn:Et.
  induction H; try (discriminate Et).
  - exists T2. 
    injection Et as Et1 Et2. subst.
    split; assumption.
  - destruct IHhas_type as [t2' [Hl' Hr']]...
Qed.


Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- (\x:S1, s2) \in (T1 -> T2) ->
     T1 <: S1 /\ (x |-> S1 ; empty) |- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst... Qed.


Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof. intros G s H.
  inversion H; intro Hv; subst; try (inversion Hv; subst).
  - left. reflexivity.
  - right. reflexivity.
  - exfalso. 
    apply abs_is_bottom_for_fun in H.
    destruct H as [T' H].
    apply sub_inversion_Bool in H.
    discriminate H.
  - left. reflexivity.
  - right. reflexivity.
  - exfalso. 
    apply unit_is_bottom_for_unit in H.
    apply sub_inversion_Bool in H.
    discriminate H.
  - exfalso.
    apply pair_is_bottom_for_pair in H.
    destruct H as [T1' [T2' H]].
    apply sub_inversion_Bool in H.
    discriminate H.
Qed.


Theorem progress : forall t T,
     empty |- t \in T   ->   value t \/ (exists t', t --> t').
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_Test *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto.
  - (* T_Pair *)
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. right. exists <{ (t1 , t2') }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. right. exists <{ (t1' , t2) }>...
  - (* T_PairFst *)
    destruct IHHt...
    + (* value pair *)
      destruct (canonical_forms_of_pair_types _ _ _ _ Ht) as [v1 [v2 Ht']]; auto.
      right. subst. exists v1. constructor.
    + destruct H as [t' H]. right. exists (tm_fst t')...
  - (* T_PairSnd *)
    destruct IHHt...
    + (* value pair *)
      destruct (canonical_forms_of_pair_types _ _ _ _ Ht) as [v1 [v2 Ht']]; auto.
      right. subst. exists v2. constructor.
    + destruct H as [t' H]. right. exists (tm_snd t')...
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
   (x |-> U ; Gamma) |- t \in T ->
   empty |- v \in U ->
   Gamma |- [x:=v]t \in T.
Proof.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - destruct (eqb_stringP x x0).
    + subst. rewrite update_eq in H. injection H as H. subst. 
      apply weakening_empty. assumption.
    + subst. rewrite update_neq in H. 
        constructor. assumption.
        assumption.
  - destruct (eqb_stringP x x0); subst.
    + constructor.
      rewrite update_shadow in Ht. 
      assumption.
    + constructor.
      apply IHHt.
      rewrite update_permute.
        reflexivity.
        assumption.
Qed.

Lemma pair_destr: forall v1 v2 T1 T2, 
  empty |- (v1, v2) \in (T1 * T2) -> 
  empty |- v1 \in T1  /\  empty |- v2 \in T2.
Proof.
  intros v1 v2 T1 T2 H.
  remember <{(v1, v2)}> as p eqn:Ep.
  remember <{(T1 * T2)}> as t eqn:Et.
  generalize dependent T1.
  generalize dependent T2.
  induction H; try (discriminate Ep); subst.
  - intros T2' T1' Hv. subst.
    apply sub_inversion_pair in H0.
    destruct H0 as [U1 [U2 [H' [Hu1 Hu2]]]]. subst.
    assert (HG: Gamma |- v1 \in U1 /\ Gamma |- v2 \in U2). {
      apply IHhas_type.
        reflexivity.
        reflexivity.
    }
    clear IHhas_type.
    destruct HG as [Hvu1 Hvu2].
    split.
    + eapply T_Sub. apply Hvu1. apply Hu1.
    + eapply T_Sub. apply Hvu2. apply Hu2.
  - intros T1' T2' Ets. injection Ets as Ets1 Ets2. subst.
    injection Ep as tv1 tv2. subst.
    split.
      assumption.
      assumption.
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
    (* Most of the cases are immediate by induction,
       and eauto takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0...
  - (* T_PairFst *)
    inversion HE; subst...
    apply pair_destr in HT.
    destruct HT as [Ht1 Ht2].
    assumption.
  - (* T_PairSnd *)
  inversion HE; subst...
  apply pair_destr in HT.
  destruct HT as [Ht1 Ht2].
  assumption.
Qed.






