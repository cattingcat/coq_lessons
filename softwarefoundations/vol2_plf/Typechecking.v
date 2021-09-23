Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

Locate "Bool".

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }>      , <{ Bool }>        => true
  | <{ T11 -> T12 }>, <{ T21 -> T22 }>  => andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _               , _                 => false
  end.


Lemma eqb_ty_refl : forall T, eqb_ty T T = true.
Proof.
  intros T. induction T; simpl.
    reflexivity.
    rewrite IHT1. rewrite IHT2. reflexivity. Qed.


Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true  ->  T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1 = T1_1->T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst... Qed.
End STLCTypes.



Module FirstTry.
Import STLCTypes.
Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{T2 -> T1}>
      | _       => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{T11 -> T12}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{Bool}>
  | <{false}> =>
      Some <{Bool}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{Bool}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.
End FirstTry.




Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)  (right associativity, at level 60).

Notation " 'return' e "  := (Some e) (at level 60).
Notation " 'fail' "  := None.

Module STLCChecker.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2 -> T1}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11 -> T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T   ->   has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert;
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.


Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T  ->  type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma x0) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T2)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T1)...
Qed.

End STLCChecker.



Module TypecheckerExtensions.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T,  eqb_ty T T = true.
Proof.
  intros T.
  induction T; simpl; auto;
    rewrite IHT1; rewrite IHT2; reflexivity. Qed.

Lemma eqb_ty__eq : forall T1 T2,  eqb_ty T1 T2 = true  ->  T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _         => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _         => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_ => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _         => fail
      end
  (* sums *)
  | <{ inl T t }> =>
      T1 <- type_check Gamma t ;;
      return <{{ (T1 + T) }}>
  | <{ inr T t }> =>
      T1 <- type_check Gamma t ;;
      return <{{ (T + T1) }}>
  | <{ case t of | inl x1 => t1 | inr x2 => t2 }> =>
      T <- type_check Gamma t ;;
      match T with 
      | <{{ (T1 + T2) }}> => 
        Tt1 <- type_check (x1 |-> T1 ; Gamma) t1 ;;
        Tt2 <- type_check (x2 |-> T2 ; Gamma) t2 ;;
        if eqb_ty Tt1 Tt2 then return Tt1 else fail
      | _                 => fail
      end
  (* lists *)
  | <{ nil T }> => return <{{ List T }}>
  | <{ h :: t }> => match type_check Gamma h, type_check Gamma t with
                    | Some <{{ Th }}>, Some <{{ List Tt }}> => 
                      if eqb_ty Th Tt then return <{{ List Tt }}> else fail
                    | _, _ => fail
                    end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      match type_check Gamma t0 with
      | Some <{{List T}}> =>
          match type_check Gamma t1,
                type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 with
          | Some T1', Some T2' =>
              if eqb_ty T1' T2' then return T1' else fail
          | _,_ => None
          end
      | _ => None
      end
  (* unit *)
  | <{ unit }> => return <{{ Unit }}>
  (* pairs *)
  | <{ (t1, t2) }> =>
        T1 <- type_check Gamma t1 ;;
        T2 <- type_check Gamma t2 ;;
        return <{{ (T1 * T2) }}>
  | <{ t.fst }> => match type_check Gamma t with
                   | Some <{{ T1 * T2 }}> => return <{{ T1 }}>
                   | _ => fail
                   end
  | <{ t.snd }> => match type_check Gamma t with
                   | Some <{{ T1 * T2 }}> => return <{{ T2 }}>
                   | _ => fail
                   end
  (* let *)
  | <{ let x = t1 in t2 }> => 
      T1 <- type_check Gamma t1 ;;
      type_check (x |-> T1 ; Gamma) t2
  (* fix *)
  | <{ fix t }> =>  match type_check Gamma t with
                    | Some <{{ (T1 -> T2) }}> => if eqb_ty T1 T2 then return T1 else fail
                    | _ => fail
                    end
  end.


Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T  ->  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  - (* inl *)
    invert_typecheck Gamma t0 T1.
  - (* inr *)
    invert_typecheck Gamma t0 T1.
  - (* case sum *)
    destruct (type_check Gamma t1) eqn:Et1.
    + destruct t eqn:Et; inversion H0.
      apply IHt1 in Et1.
        remember (s |-> t0_1 ; Gamma) as Gamma'.
        invert_typecheck Gamma' t2 Tt1.
        remember (s0 |-> t0_2 ; Gamma) as Gamma'.
        invert_typecheck Gamma' t3 Tt2.
      symmetry in HeqTO. apply IHt2 in HeqTO.
      symmetry in HeqTO0. apply IHt3 in HeqTO0.
      case_equality Tt1 Tt2.
    + discriminate H0.
  - (* nil *)
    simpl in Htc.
    constructor.
  - (* cons *)
    invert_typecheck Gamma t1 Th.
    symmetry in HeqTO. apply IHt1 in HeqTO.
    destruct (type_check Gamma t2) eqn:Et2; inversion H1.
    destruct t eqn:Et; inversion H2.
    case_equality Th t0.
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* unit *) constructor.
  - (* pair *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - (* fst *)
    destruct (type_check Gamma t) eqn:Et; inversion H0.
    apply IHt in Et.
    destruct t0 eqn:Et0; inversion H0; subst.
    apply T_PairFst with t1_2. 
    assumption.
  - (* snd *)
    destruct (type_check Gamma t) eqn:Et; inversion H0.
    apply IHt in Et.
    destruct t0 eqn:Et0; inversion H0; subst.
    apply T_PairSnd with t1_1. 
    assumption.
  - (* let *)
    invert_typecheck Gamma t1 T1.
  - (* fix *)
    destruct (type_check Gamma t) eqn:Et; inversion H0.
    apply IHt in Et.
    destruct t0 eqn:Et0; inversion H0; subst.
    case_equality t1_1 t1_2.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T  ->  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma x0); [assumption| solve_by_invert].
Qed.

End TypecheckerExtensions.


Module StepFunction.
Import MoreStlc.
Import STLCExtended.


Fixpoint is_value (t: tm) : bool :=
  match t with 
  | <{ \ _ : _, _ }> => true
  | tm_const _ => true
  | <{inl _ v}> => is_value v
  | <{inr _ v}> => is_value v
  | <{nil _}> => true
  | <{v1 :: v2}> => andb (is_value v1) (is_value v2)
  | <{unit}> => true
  | <{(v1, v2)}> => andb (is_value v1) (is_value v2)
  | _ => false
  end.

(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm := 
  match t with 
  | tm_var _ => fail
  | <{ \ _ : _, _ }> => fail
  | tm_const _ => fail
  | <{ nil _ }> => fail
  | <{ unit }> => fail
  | <{t1 t2}> => 
    match is_value t1 , is_value t2 with
    | true, true => 
      match t1 with 
      | <{ (\x:T2, t) }> => return <{ [x:=t2]t }>
      | _ => fail
      end
    | true, false =>
      t2' <- stepf t2 ;;
      return <{t1 t2'}>
    | false, _ =>
      t1' <- stepf t1 ;;
      return <{t1' t2}>
    end
  | <{succ t1}> =>
    if is_value t1 
      then
        match t1 with
        | tm_const n => return (tm_const (S n))
        | _ => fail
        end
      else
        t1' <- stepf t1 ;;
        return <{succ t1'}>
  | <{pred t1}> =>
    if is_value t1 
      then
        match t1 with
        | tm_const n => return (tm_const (n - 1))
        | _ => fail
        end
      else
        t1' <- stepf t1 ;;
        return <{pred t1'}>
  | <{t1 * t2}> => 
    match is_value t1 , is_value t2 with
    | true, true => 
      match t1, t2 with 
      | tm_const n1, tm_const n2 => return (tm_const (n1 * n2))
      | _, _ => fail
      end
    | true, false =>
      t2' <- stepf t2 ;;
      return <{t1 * t2'}>
    | false, _ =>
      t1' <- stepf t1 ;;
      return <{t1' * t2}>
    end
  | <{if0 t1 then t2 else t3}> =>
      if is_value t1
        then 
          match t1 with
          | tm_const 0 => return t2
          | tm_const (S _) => return t3
          | _ => fail
          end
        else 
          t1' <- stepf t1 ;;
          return <{if0 t1' then t2 else t3}>
  | <{inl T2 t1}> =>
      t1' <- stepf t1 ;;
      return <{inl T2 t1'}>
  | <{inr T1 t2}> => 
      t2' <- stepf t2 ;;
      return <{inr T1 t2'}>
  | <{case t0 of | inl x1 => t1 | inr x2 => t2}> =>
      if is_value t0
        then 
          match t0 with
          | <{inl T2 v0}> => return <{ [x1:=v0]t1 }>
          | <{inr T1 v0}> => return <{ [x2:=v0]t2 }>
          | _ => fail
          end
        else 
          t0' <- stepf t0 ;;
          return <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | <{t1 :: t2}> =>
      match is_value t1 , is_value t2 with
      | true, true => fail
      | true, false =>
        t2' <- stepf t2 ;;
        return <{t1 :: t2'}>
      | false, _ =>
        t1' <- stepf t1 ;;
        return <{t1' :: t2}>
      end
  | <{case t1 of | nil => t2 | x1 :: x2 => t3}> =>
      if is_value t1
        then 
          match t1 with
          | <{ nil T1 }> => return <{ t2 }>
          | <{v1 :: vl}> => return <{ [x2 := vl] ([x1 := v1] t3) }>
          | _ => fail
          end
        else 
          t1' <- stepf t1 ;;
          return <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | <{(t1 , t2)}> =>
      match is_value t1 , is_value t2 with
      | true, true => fail
      | true, false =>
        t2' <- stepf t2 ;;
        return <{(t1 , t2')}>
      | false, _ =>
        t1' <- stepf t1 ;;
        return <{(t1' , t2)}>
      end
  | <{ t.fst }> =>
      if is_value t 
        then
          match t with 
          | <{(t1, t2)}> => return t1
          | _ => fail
          end
        else
          t' <- stepf t ;;
          return <{ t'.fst }>
  | <{ t.snd }> =>
      if is_value t 
        then
          match t with 
          | <{(t1, t2)}> => return t2
          | _ => fail
          end
        else
          t' <- stepf t ;;
          return <{ t'.snd }>
  | <{ let v = t1 in t2 }> =>
      if is_value t1
        then return <{ [v:=t1]t2 }>
        else 
          t1' <- stepf t1 ;;
          return  <{ let v = t1' in t2 }>
  | <{ fix t }> =>
      if is_value t 
        then
          match t with 
          | <{(\f:T, t)}> => return <{ [f:=fix (\f:T, t)]t }>
          | _ => fail
          end
        else
          t' <- stepf t ;;
          return <{ fix t' }>
  end.

Lemma sound_is_value: forall t,
  is_value t = true   ->   value t.
Proof.
  intro t.
  induction t; intro H; simpl in H; 
    try (discriminate H);
    try (constructor);
    auto.
  - Search (?x && ?y = true -> ?x = true /\ ?y = true).
    apply andb_prop in H. destruct H. auto.
  - apply andb_prop in H. destruct H. auto.
  - apply andb_prop in H. destruct H. auto.
  - apply andb_prop in H. destruct H. auto.
Qed.
Hint Resolve sound_is_value : core.

Lemma sound_is_value_ref: forall t,
  value t   ->   is_value t = true.
Proof.
  intro t.
  induction t; intro H; simpl in H; unfold is_value; simpl; try (reflexivity); try (inversion H).
  - subst. apply IHt. assumption.
  - subst. apply IHt. assumption.
  - subst. 
    Search (?x = true /\ ?y = true -> ?x && ?y = true).
    apply andb_true_intro.
    split. 
      apply IHt1. assumption.
      apply IHt2. assumption.
  - apply andb_true_intro.
    split. 
      apply IHt1. assumption.
      apply IHt2. assumption.
Qed.
Hint Resolve sound_is_value_ref : core.

Lemma string_der_refl: forall s, eqb_string s s = true.
Proof. intro s. unfold eqb_string. destruct (string_dec s s); auto. Qed.

(* Soundness of stepf. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'   ->   t --> t'.
Proof.
  intro t.
  induction t; intros t' H; simpl in H; try (discriminate H).
  - destruct (is_value t1) eqn:Es1.
    + (* t1 val *)
      destruct (is_value t2) eqn:Es2.
      * (* t2 val *)
        destruct t1; try (discriminate H).
        injection H as H. rewrite <- H. constructor. 
        apply sound_is_value. assumption.
      * destruct (stepf t2); try (discriminate H).
        injection H as H. rewrite <- H. constructor.
          apply sound_is_value. assumption.
          apply IHt2. reflexivity.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt1. reflexivity.
  - destruct (is_value t) eqn:Es.
    + destruct t eqn: Et; try (discriminate H).
      injection H as H. subst. constructor.
    + destruct (stepf t); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt. reflexivity.
  - destruct (is_value t) eqn:Es.
    + destruct t eqn: Et; try (discriminate H).
      injection H as H. subst. constructor.
    + destruct (stepf t); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt. reflexivity.
  - destruct (is_value t1) eqn:Es1.
    + (* t1 val *)
      destruct (is_value t2) eqn:Es2.
      * (* t2 val *)
        destruct t1; try (discriminate H).
        destruct t2 eqn: Et; try (discriminate H).
        injection H as H. rewrite <- H. constructor. 
      * destruct (stepf t2); try (discriminate H).
        injection H as H. rewrite <- H. constructor.
          apply sound_is_value. assumption.
          apply IHt2. reflexivity.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt1. reflexivity.
  - destruct (is_value t1) eqn:Es.
    + destruct t1 eqn: Et; try (discriminate H).
      destruct n.
      -- injection H as H. subst. constructor.
      -- injection H as H. subst. constructor.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt1. reflexivity.
  - destruct (stepf t0) eqn:Es.
    + injection H as H. subst. constructor.
      apply IHt. reflexivity.
    + discriminate H.
  - destruct (stepf t0) eqn:Es.
    + injection H as H. subst. constructor.
      apply IHt. reflexivity.
    + discriminate H.
  - destruct (is_value t1) eqn:Es.
    + destruct t1 eqn: Et; try (discriminate H); injection H as H.
      -- subst. constructor.
         apply sound_is_value. assumption.
      -- subst. constructor.
         apply sound_is_value. assumption.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt1. reflexivity.
  - destruct (is_value t1) eqn:Es1.
    + (* t1 val *)
      destruct (is_value t2) eqn:Es2.
      * (* t2 val *) discriminate H.
      * destruct (stepf t2); try (discriminate H).
        injection H as H. rewrite <- H. constructor.
          apply sound_is_value. assumption.
          apply IHt2. reflexivity.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt1. reflexivity.
  - destruct (is_value t1) eqn:Es.
    + destruct t1 eqn: Et; try (discriminate H); injection H as H.
      -- subst. constructor.
      -- subst. simpl in Es. apply andb_prop in Es. destruct Es as [Es1 Es2]. constructor.
         auto.
         auto.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt1. reflexivity.
  - destruct (is_value t1) eqn:Es1.
    + (* t1 val *)
      destruct (is_value t2) eqn:Es2.
      * (* t2 val *) discriminate H.
      * destruct (stepf t2); try (discriminate H).
        injection H as H. rewrite <- H. constructor.
          apply sound_is_value. assumption.
          apply IHt2. reflexivity.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt1. reflexivity.
  - destruct (is_value t) eqn:Es.
    + destruct t eqn: Et; try (discriminate H).
      injection H as H. subst.
      simpl in Es. apply andb_prop in Es. destruct Es as [Es1 Es2].
      constructor.
         auto.
         auto.
    + destruct (stepf t); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt. reflexivity.
  - destruct (is_value t) eqn:Es.
    + destruct t eqn: Et; try (discriminate H).
      injection H as H. subst.
      simpl in Es. apply andb_prop in Es. destruct Es as [Es1 Es2].
      constructor.
         auto.
         auto.
    + destruct (stepf t); try (discriminate H).
      injection H as H. rewrite <- H. constructor.
      apply IHt. reflexivity.
  - destruct (is_value t1) eqn:Es.
    + injection H as H. subst. constructor. auto.
    + destruct (stepf t1); try (discriminate H).
      injection H as H. subst.
      constructor.
      apply IHt1. reflexivity.
  - destruct (is_value t) eqn:Es.
    + destruct t; try (discriminate H).
      injection H as H. subst. constructor.
    + destruct (stepf t); try (discriminate H).
      injection H as H. subst.
      constructor.
      apply IHt. reflexivity.
Qed.

Search (?a && ?b = ?b && ?a).
Lemma isnt_value: forall t t', 
  t --> t'  ->  is_value t = false.
Proof.
  intros t t' H.
  induction H; simpl; 
    try reflexivity;
    try assumption.
  - rewrite IHstep. reflexivity.
  - rewrite IHstep. rewrite andb_comm. reflexivity.
  - rewrite IHstep. reflexivity.
  - rewrite IHstep. rewrite andb_comm. reflexivity.
Qed.


(* Completeness of stepf. *)
Theorem complete_stepf : forall t t',
    t --> t'   ->   stepf t = Some t'.
Proof. 
  intros t t' H.
  induction H; simpl.
  - apply sound_is_value_ref in H. rewrite H. reflexivity.
  - apply isnt_value in H. rewrite H. rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    apply isnt_value in H0. rewrite H0.
    rewrite IHstep. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    apply isnt_value in H0. rewrite H0.
    rewrite IHstep. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHstep. reflexivity.
  - rewrite IHstep. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    apply isnt_value in H0. rewrite H0.
    rewrite IHstep. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    apply sound_is_value_ref in H0. rewrite H0.
    simpl. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    apply isnt_value in H0. rewrite H0.
    rewrite IHstep. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    apply sound_is_value_ref in H0. rewrite H0.
    simpl. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    apply sound_is_value_ref in H0. rewrite H0.
    simpl. reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - apply sound_is_value_ref in H. rewrite H.
    reflexivity.
  - apply isnt_value in H. rewrite H.
    rewrite IHstep. reflexivity.
  - reflexivity.
Qed.

End StepFunction.



Module StlcImpl.
Import StepFunction.
(*  Using the Imp parser described in the 
    ImpParser chapter of Logical Foundations as a 
    guide, build a parser for extended STLC programs. 
    Combine it with the typechecking and stepping functions 
    from the above exercises to yield a complete typechecker 
    and interpreter for this language. *)
End StlcImpl.

