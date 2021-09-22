Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

Module STLCExtended.


Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat : ty
  | Ty_Sum : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., case t0 of inl x1 => t1 | inr x2 => t2 *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., case t1 of | nil => t2 | x::y => t3 *)
  (* unit *)
  | tm_unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* let *)
  | tm_let : string -> tm -> tm -> tm
         (* i.e., let x = t1 in t2 *)
  (* fix *)
  | tm_fix : tm -> tm.



Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
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
Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.
Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               x2 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).
Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc_ty at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).
Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc at level 0).
Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).


Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{ \y:T, [x:=s]t1 }>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x:=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x:=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x:=s] t0) of
         | inl y1 => { if eqb_string x y1 then t1 else <{ [x:=s] t1 }> }
         | inr y2 => {if eqb_string x y2 then t2 else <{ [x:=s] t2 }> } }>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if eqb_string x y1 then
           t3
         else if eqb_string x y2 then t3
              else <{ [x:=s] t3 }> } }>
  (* unit *)
  | <{unit}> => <{unit}>

  (* pairs *)
  | <{ ( l , r ) }> => <{ ( [x:=s]l , [x:=s]r ) }>
  | <{ t.fst }> => <{ ([x:=s]t).fst }>
  | <{ t.snd }> => <{ ([x:=s]t).snd }>

  (* let *)
  | <{ let v = t1 in t2 }> => if eqb_string x v 
      then <{ let v = [x:=s]t1 in t2 }>
      else <{ let v = [x:=s]t1 in [x:=s]t2 }>
  (* fix *)
  | <{ fix t }> => <{ fix [x:=s]t }>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).



Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{inl T1 v}>
  | v_inr : forall v T1,
      value v ->
      value <{inr T1 v}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>
  (* A unit is always a value *)
  | v_unit : value <{unit}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.


Hint Constructors value : core.
Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
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
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ {S n} }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ {n - 1} }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ {n1 * n2} }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 0 then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 {S n} then t2 else t3}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{inl T2 t1}> --> <{inl T2 t1'}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{inr T1 t2}> --> <{inr T1 t2'}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{case t0 of | inl x1 => t1 | inr x2 => t2}> -->
        <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x1:=v0]t1 }>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x2:=v0]t2 }>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         --> <{ [x2 := vl] ([x1 := v1] t3) }>
  (* pairs *)
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
       value v1 ->
       value v2 ->
       <{ (v1 , v2).fst }> --> <{ v1 }>
  | ST_PairSndStep : forall t t',
       t --> t' ->
       <{ t.snd }> --> <{ t'.snd }>
  | ST_PairSnd : forall v1 v2,
       value v1 ->
       value v2 ->
       <{ (v1 , v2).snd }> --> <{ v2 }>
  (* let *)
  | ST_LetStep : forall v t1 t1' t2,
       t1 --> t1' ->
       <{ let v = t1 in t2 }> --> <{ let v = t1' in t2 }>
  | ST_LetElim : forall v v1 t2,
       value v1 ->
       <{ let v = v1 in t2 }> --> <{ [v:=v1]t2 }>
  (* fix *)
  | ST_FixStep : forall t t',
       t --> t' ->
       <{ fix t }> --> <{ fix t' }>
  | ST_Fix : forall t f T,
    <{ fix (\f:T, t) }> --> <{ [f:=fix (\f:T, t)]t }>

  where "t '-->' t'" := (step t t').
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors step : core.


Definition context := partial_map ty.
Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
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
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |- n \in Nat
  | T_Succ : forall Gamma t,
      Gamma |- t \in Nat ->
      Gamma |- succ t \in Nat
  | T_Pred : forall Gamma t,
      Gamma |- t \in Nat ->
      Gamma |- pred t \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in Nat ->
      Gamma |- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T0 ->
      Gamma |- t3 \in T0 ->
      Gamma |- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- (inl T2 t1) \in (T1 + T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 \in T2 ->
      Gamma |- (inr T1 t2) \in (T1 + T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |- t0 \in (T1 + T2) ->
      (x1 |-> T1 ; Gamma) |- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |- t2 \in T3 ->
      Gamma |- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (List T1) ->
      Gamma |- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 \in (List T1) ->
      Gamma |- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |- t3 \in T2 ->
      Gamma |- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit

  (* pairs *)
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
  (* let *)
  | T_Let: forall Gamma v t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      (v |-> T1 ; Gamma) |- t2 \in T2 ->
      Gamma |- (let v = t1 in t2) \in T2
  (* fix *)
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 \in (T1 -> T1) ->
      Gamma |- (fix t1) \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.


Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".



Hint Extern 2 (has_type _ (tm_app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.




Module Numtest.
(* tm_test0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
Definition test :=
  <{if0
    (pred
      (succ
        (pred
          (2 * 0))))
    then 5
    else 6}>.
Example typechecks :
  empty |- test \in Nat.
Proof.
  unfold test.
  (* This typing derivation is quite deep, so we need
     to increase the max search depth of auto from the
     default 5 to 10. *)
  auto 10.
Qed.

Example numtest_reduces :
  test -->* 5.
Proof.
  unfold test. normalize.
Qed.
End Numtest.


Module Prodtest.
(* ((5,6),7).fst.tm_snd *)
Definition test :=
  <{((5,6),7).fst.snd}>.
Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. Qed.
(* GRADE_THEOREM 0.25: typechecks *)
Example reduces :
  test -->* 6.
Proof.
  unfold test. normalize.
Qed.
(* GRADE_THEOREM 0.25: reduces *)
End Prodtest.


Module LetTest.
(* let x = pred 6 in succ x *)
Definition test :=
  <{let x = (pred 6) in (succ x)}>.
Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. Qed.
(* GRADE_THEOREM 0.25: typechecks *)
Example reduces :
  test -->* 6.
Proof.
  unfold test. normalize.
Qed.
(* GRADE_THEOREM 0.25: reduces *)
End LetTest.


Module Sumtest1.
Definition test :=
  <{case (inl Nat 5) of
    | inl x => x
    | inr y => y}>.
Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. Qed.
Example reduces :
  test -->* 5.
Proof.
  unfold test. normalize.
Qed.
End Sumtest1.

Module Sumtest2.
Definition test :=
  <{let processSum =
    (\x:Nat + Nat,
      case x of
       | inl n => n
       | inr n => (if0 n then 1 else 0)) in
    (processSum (inl Nat 5), processSum (inr Nat 5))}>.
Example typechecks :
  empty |- test \in (Nat * Nat).
Proof. unfold test. eauto 15. Qed.
Example reduces :
  test -->* <{(5, 0)}>.
Proof.
  unfold test. normalize.
Qed.
End Sumtest2.



Module ListTest.
Definition test :=
  <{let l = (5 :: 6 :: (nil Nat)) in
    case l of
    | nil => 0
    | x :: y => (x * x)}>.
Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 20. Qed.
Example reduces :
  test -->* 25.
Proof.
  unfold test. normalize.
Qed.
End ListTest.


Module FixTest1.
Definition fact :=
  <{fix
      (\f:Nat -> Nat,
        \a:Nat,
         if0 a then 1 else (a * (f (pred a))))}>.

Example typechecks :
  empty |- fact \in (Nat -> Nat).
Proof. unfold fact. auto 10. Qed.

Example reduces :
  <{fact 4}> -->* 24.
Proof.
  unfold fact. normalize.
Qed.
End FixTest1.

Module FixTest2.
Definition map :=
  <{ \g:Nat -> Nat,
       fix
         (\f:(List Nat) -> (List Nat),
            \l:List Nat,
               case l of
               | nil => nil Nat
               | x::l => ((g x)::(f l)))}>.
Example typechecks :
  empty |- map \in
    ((Nat -> Nat) -> ((List Nat) -> (List Nat))).
Proof. unfold map. auto 10. Qed.

Example reduces :
  <{map (\a:Nat, succ a) (1 :: 2 :: (nil Nat))}>
  -->* <{2 :: 3 :: (nil Nat)}>.
Proof. unfold map. normalize. Qed.
End FixTest2.

Module FixTest3.
Definition equal :=
  <{fix
        (\eq:Nat -> Nat -> Nat,
           \m:Nat, \n:Nat,
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n))))}>.
Example typechecks :
  empty |- equal \in (Nat -> Nat -> Nat).
Proof. unfold equal. auto 10. Qed.

Example reduces :
  <{equal 4 4}> -->* 1.
Proof.  unfold equal. normalize. Qed.

Example reduces2 :
  <{equal 4 5}> -->* 0.
Proof. unfold equal. normalize. Qed.
End FixTest3.

Module FixTest4.
Definition eotest :=
<{let evenodd =
         fix
           (\eo: ((Nat -> Nat) * (Nat -> Nat)),
              (\n:Nat, if0 n then 1 else (eo.snd (pred n)),
               \n:Nat, if0 n then 0 else (eo.fst (pred n)))) in
    let even = evenodd.fst in
    let odd = evenodd.snd in
    (even 3, even 4)}>.
Example typechecks :
  empty |- eotest \in (Nat * Nat).
Proof. unfold eotest. eauto 30. Qed.

Example reduces :
  eotest -->* <{(0, 1)}>.
Proof. unfold eotest. normalize. Qed.
End FixTest4.
End Examples.



Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be
       T_Var, since it can never be the case that
       empty |- x \in T (since the context is empty). *)
    discriminate H.
  - (* T_Abs *)
    (* If the T_Abs rule was the last used, then
       t = \ x0 : T2, t1, which is a value. *)
    left...
  - (* T_App *)
    (* If the last rule applied was T_App, then t = t1 t2,
       and we know from the form of the rule that
         empty |- t1 \in T1 -> T2
         empty |- t2 \in T1
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        (* If both t1 and t2 are values, then we know that
           t1 = \x0 : T0, t11, since abstractions are the
           only values that can have an arrow type.  But
           (\x0 : T0, t11) t2 --> [x:=t2]t11 by ST_AppAbs. *)
        destruct H; try solve_by_invert.
        exists <{ [x0 := t2]t1 }>...
      * (* t2 steps *)
        (* If t1 is a value and t2 --> t2',
           then t1 t2 --> t1 t2' by ST_App2. *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      (* Finally, If t1 --> t1', then t1 t2 --> t1' t2
         by ST_App1. *)
      destruct H as [t1' Hstp]. exists <{t1' t2}>...
  - (* T_Nat *)
    left...
  - (* T_Succ *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists <{ {S n} }>...
    + (* t1 steps *)
      destruct H as [t' Hstp].
      exists <{succ t'}>...
  - (* T_Pred *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists <{ {n - 1} }>...
    + (* t1 steps *)
      destruct H as [t' Hstp].
      exists <{pred t'}>...
  - (* T_Mult *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      *  (* t2 is a value *)
        destruct H; try solve_by_invert.
        destruct H0; try solve_by_invert.
        exists <{ {n * n0} }>...
      *  (* t2 steps *)
        destruct H0 as [t2' Hstp].
        exists <{t1 * t2'}>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{t1' * t2}>...
  - (* T_Test0 *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      destruct n as [|n'].
      *  (* n1=0 *)
        exists t2...
      *  (* n1<>0 *)
        exists t3...
    + (* t1 steps *)
      destruct H as [t1' H0].
      exists <{if0 t1' then t2 else t3}>...
  - (* T_Inl *)
    destruct IHHt...
    + (* t1 steps *)
      right. destruct H as [t1' Hstp]...
      (* exists (tm_inl _ t1')... *)
  - (* T_Inr *)
    destruct IHHt...
    + (* t1 steps *)
      right. destruct H as [t1' Hstp]...
      (* exists (tm_inr _ t1')... *)
  - (* T_Case *)
    right.
    destruct IHHt1...
    + (* t0 is a value *)
      destruct H; try solve_by_invert.
      *  (* t0 is inl *)
        exists <{ [x1:=v]t1 }>...
      *  (* t0 is inr *)
        exists <{ [x2:=v]t2 }>...
    + (* t0 steps *)
      destruct H as [t0' Hstp].
      exists <{case t0' of | inl x1 => t1 | inr x2 => t2}>...
  - (* T_Nil *)
    left...
  - (* T_Cons *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2...
      *  (* tail steps *)
        right. destruct H0 as [t2' Hstp].
        exists <{t1 :: t2'}>...
    + (* head steps *)
      right. destruct H as [t1' Hstp].
      exists <{t1' :: t2}>...
  - (* T_Lcase *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      *  (* t1=tm_nil *)
        exists t2... 
      *  (* t1=tm_cons v1 v2 *)
        exists <{ [x2:=v2]([x1:=v1]t3) }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{case t1' of | nil => t2 | x1 :: x2 => t3}>...
  - (* T_Unit *)
    left...
  -  (* Pair *)
    destruct IHHt1...
    +  (* t1 is a value *)
      destruct IHHt2...
      *  (* t2 is a step *)
        destruct H0 as [t2' Hstp].
        right. exists <{ (t1 , t2') }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      right. exists <{ (t1' , t2) }>...
  - (* Fst *)
    destruct IHHt...
    +  (* t1 is a value *)
      destruct H; try solve_by_invert.
      right. exists <{ v1 }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      right. exists <{ (t1').fst }>...
  - (* Snd *)
    destruct IHHt...
    +  (* t1 is a value *)
      destruct H; try solve_by_invert.
      right. exists <{ v2 }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      right. exists <{ (t1').snd }>...
  - (* Let *)
    right.
    destruct IHHt1...
    +  (* t1 is a step *)
      destruct H; try solve_by_invert.
      exists (tm_let v x0 t2)...
  - (* Fix *)
    destruct IHHt...
    +  (* t1 is a value *)
      destruct H; try solve_by_invert.
      right. exists <{ [x0:=fix (\x0:T2, t1)]t1 }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      right. exists <{ fix t1' }>...
Qed.

Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma |- t \in T ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto 7 using inclusion_update.
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
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term t.  Most cases follow
     directly from the IH, with the exception of var
     and abs. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
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
  - (* tm_case *)
    rename s into x1, s0 into x2.
    eapply T_Case...
    + (* left arm *)
      destruct (eqb_stringP x x1); subst.
      *  (* x = x1 *)
        rewrite update_shadow in H8. assumption.
      *  (* x <> x1 *)
        apply IHt2.
        rewrite update_permute; auto.
    + (* right arm *)
      destruct (eqb_stringP x x2); subst.
      *  (* x = x2 *)
        rewrite update_shadow in H9. assumption.
      *  (* x <> x2 *)
        apply IHt3.
        rewrite update_permute; auto.
  - (* tm_lcase *)
    rename s into y1, s0 into y2.
    eapply T_Lcase...
    destruct (eqb_stringP x y1); subst.
    + (* x=y1 *)
      destruct (eqb_stringP y2 y1); subst.
      *  (* y2=y1 *)
        repeat rewrite update_shadow in H9.
        rewrite update_shadow.
        assumption.
      * rewrite update_permute in H9; [|assumption].
        rewrite update_shadow in H9.
        rewrite update_permute; assumption.
    + (* x<>y1 *)
      destruct (eqb_stringP x y2); subst.
      * (* x=y2 *)
        rewrite update_shadow in H9.
        assumption.
      * (* x<>y2 *)
        apply IHt3.
        rewrite (update_permute _ _ _ _ _ _ n0) in H9.
        rewrite (update_permute _ _ _ _ _ _ n) in H9.
        assumption.
  - (*let*)
    destruct (eqb_stringP x s); subst.
    ++ eapply T_Let.
      + apply IHt1. apply H5.
      + rewrite update_shadow in H6. assumption.
    ++ eapply T_Let.
      + apply IHt1. apply H5.
      + apply IHt2. rewrite update_permute in H6; assumption.
Qed.


Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t --> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  (* Proof: By induction on the given typing derivation.  Many
     cases are contradictory (T_Var, T_Abs).  We show just
     the interesting ones. Again, we refer the reader to
     StlcProp.v for explanations. *)
  induction HT;
    intros t' HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
  (* T_Case *)
  - (* ST_CaseInl *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* ST_CaseInr *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* T_Lcase *)
    + (* ST_LcaseCons *)
      inversion HT1; subst.
      apply substitution_preserves_typing with <{{List T1}}>...
      apply substitution_preserves_typing with T1...
  (* fst and snd *)
  - inversion HE; subst...
    inversion HT...
  - inversion HE; subst...
    inversion HT...
  (* let *)
  - apply substitution_preserves_typing with T1...
  (* fix *)
  - inversion HT; subst.
    apply substitution_preserves_typing with T1...
Qed.


End STLCExtended.
