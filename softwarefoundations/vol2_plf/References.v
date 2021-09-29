Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From Coq Require Import Lists.List.
Import Nat.

Module STLCRef.

Inductive ty : Type :=
  | Ty_Nat : ty
  | Ty_Unit : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Ref : ty -> ty.

Inductive tm : Type :=
  (* STLC with numbers: *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm
  (* New terms: *)
  | tm_unit : tm
  | tm_ref : tm -> tm
  | tm_deref : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc : nat -> tm.


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
Notation "{ x }" := x (in custom stlc at level 0, x constr).
Notation "'Unit'" := (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).
Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0, x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0, x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1, left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.
Notation "'Ref' t" := (Ty_Ref t) (in custom stlc at level 4).
Notation "'loc' x" := (tm_loc x) (in custom stlc at level 2).
Notation "'ref' x" := (tm_ref x) (in custom stlc at level 2).
Notation "'!' x " := (tm_deref x) (in custom stlc at level 2).
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom stlc at level 21).


Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
      value <{ loc l }>.
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
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
  (* unit *)
  | <{ unit }> =>
    <{ unit }>
  (* references *)
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Definition tseq t1 t2 :=
  <{ (\ x : Unit, t2) t1 }>.
Notation "t1 ; t2" := (tseq t1 t2) (in custom stlc at level 3).




Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=  nth n st <{ unit }>.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil     => nil
  | h :: t  =>
    match n with
    | O     => x :: t
    | S n'  => h :: replace n' x t
    end
  end.

Lemma replace_nil : forall A n (x: A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : forall A n x (l: list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st = nil *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l; simpl...
    apply IHst'. simpl in Hlen. lia.
Qed.

Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  - (* l1 = 0 *)
    destruct st.
    + (* st =  *) rewrite replace_nil...
    + (* st = _ :: _ *) destruct l2... contradict Hneq...
  - (* l1 = S l1' *)
    destruct st as [|t2 st2].
    + (* st =  *) destruct l2...
    + (* st = t2 :: st2 *)
      destruct l2...
      simpl; apply IHl1'...
Qed.



Reserved Notation "t '/' st '-->' t' '/' st'"  (at level 40, st at level 39, t' at level 39).
Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2 st,
         value v2 ->
         <{ (\x : T2, t1) v2 }> / st --> <{ [x := v2] t1 }> / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 t2 }> / st --> <{ t1' t2 }> / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 t2 }> / st --> <{ v1 t2' }> / st'
  (* numbers *)
  | ST_SuccNat : forall (n : nat) st,
         <{ succ n }> / st --> tm_const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ succ t1 }> / st --> <{ succ t1' }> / st'
  | ST_PredNat : forall (n : nat) st,
         <{ pred n }> / st --> tm_const (n - 1) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ pred t1 }> / st --> <{ pred t1' }> / st'
  | ST_MultNats : forall (n1 n2 : nat) st,
      <{ n1 * n2 }> / st --> tm_const (n1 * n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st --> t1' / st' ->
         <{ t1 * t2 }> / st --> <{ t1' * t2 }> / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 * t2 }> / st --> <{ v1 * t2' }> / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         <{ if0 t1 then t2 else t3 }> / st --> <{ if0 t1' then t2 else t3 }> / st'
  | ST_If0_Zero : forall t2 t3 st,
         <{ if0 0 then t2 else t3 }> / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         <{ if0 {S n} then t2 else t3 }> / st --> t3 / st
  (* references *)
  | ST_RefValue : forall v st,
         value v ->
         <{ ref v }> / st --> <{ loc { length st } }> / (st ++ v::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ref t1 }> / st --> <{ ref t1' }> / st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         <{ !(loc l) }> / st --> <{ { store_lookup l st } }> / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ! t1 }> / st --> <{ ! t1' }> / st'
  | ST_Assign : forall v l st,
         value v ->
         l < length st ->
         <{ (loc l) := v }> / st --> <{ unit }> / replace l v st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 := t2 }> / st --> <{ t1' := t2 }> / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 := t2 }> / st --> <{ v1 := t2' }> / st'
where "t '/' st '-->' t' '/' st'" := (step (t,st) (t',st')).
Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t '/' st '-->*' t' '/' st'" := (multistep (t,st) (t',st'))
                                         (at level 40, st at level 39, t' at level 39).

Definition context := partial_map ty.

Definition store_ty := list ty.

Definition store_Tlookup (n:nat) (ST:store_ty) :=  nth n ST <{ Unit }>.


Reserved Notation "Gamma ';' ST '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc at level 0).
Inductive has_type (ST : store_ty) : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma ; ST |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      update Gamma x T2 ; ST |- t1 \in T1 ->
      Gamma ; ST |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma ; ST |- t1 \in (T2 -> T1) ->
      Gamma ; ST |- t2 \in T2 ->
      Gamma ; ST |- t1 t2 \in T1
  | T_Nat : forall Gamma (n : nat),
      Gamma ; ST |- n \in Nat
  | T_Succ : forall Gamma t1,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- succ t1 \in Nat
  | T_Pred : forall Gamma t1,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- pred t1 \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- t2 \in Nat ->
      Gamma ; ST |- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- t2 \in T0 ->
      Gamma ; ST |- t3 \in T0 ->
      Gamma ; ST |- if0 t1 then t2 else t3 \in T0
  | T_Unit : forall Gamma,
      Gamma ; ST |- unit \in Unit
  | T_Loc : forall Gamma l,
      l < length ST ->
      Gamma ; ST |- (loc l) \in (Ref {store_Tlookup l ST })
  | T_Ref : forall Gamma t1 T1,
      Gamma ; ST |- t1 \in T1 ->
      Gamma ; ST |- (ref t1) \in (Ref T1)
  | T_Deref : forall Gamma t1 T1,
      Gamma ; ST |- t1 \in (Ref T1) ->
      Gamma ; ST |- (! t1) \in T1
  | T_Assign : forall Gamma t1 t2 T2,
      Gamma ; ST |- t1 \in (Ref T2) ->
      Gamma ; ST |- t2 \in T2 ->
      Gamma ; ST |- (t1 := t2) \in Unit
where "Gamma ';' ST '|-' t '\in' T" := (has_type ST Gamma t T).
Hint Constructors has_type : core.



Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st -> empty; ST |- { store_lookup l st } \in {store_Tlookup l ST }).

Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).
Hint Constructors extends : core.

 Lemma extends_lookup : forall l ST ST',
  l < length ST  ->  extends ST' ST  ->  store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto.
  intros l ST.
  generalize dependent l.
  induction ST as [|a ST2]; intros l ST' Hlen HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; lia.
Qed.

Lemma length_extends : forall l ST ST',
  l < length ST  ->  extends ST' ST  ->  l < length ST'.
Proof.
  intros. generalize dependent l. induction H0; intros l Hlen.
    - inversion Hlen.
    - simpl in *.
      destruct l; try lia.
        apply lt_n_S. apply IHextends. lia.
Qed.

Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
Proof.
  induction ST; intros T.
  auto.
  simpl. auto.
Qed.

Lemma extends_refl : forall ST,
  extends ST ST.
Proof.
  induction ST; auto.
Qed.



Definition preservation_theorem := forall ST t t' T st st',
  empty ; ST |- t \in T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
     extends ST' ST           /\
     empty ; ST' |- t' \in T  /\
     store_well_typed ST' st'.



Lemma weakening : forall Gamma Gamma' ST t T,
     inclusion Gamma Gamma' ->
     Gamma ; ST |- t \in T ->
     Gamma' ; ST |- t \in T.
Proof.
  intros Gamma Gamma' ST t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma ST t T,
     empty ; ST |- t \in T ->
     Gamma ; ST |- t \in T.
Proof.
  intros Gamma ST t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x U t v T,
  (update Gamma x U); ST |- t \in T ->
  empty ; ST |- v \in U ->
  Gamma ; ST |- [x:=v]t \in T.
Proof.
  intros Gamma ST x U t v T Ht Hv.
  generalize dependent Gamma. 
  generalize dependent T.
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
    rename s into y.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  empty ; ST |- t \in {store_Tlookup l ST} ->
  store_well_typed ST (replace l t st).
Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  destruct (l' =? l) eqn: Heqll'.
  - (* l' = l *)
    apply eqb_eq in Heqll'; subst.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    apply eqb_neq in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H0...
Qed.


Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  Gamma ; ST |- t \in T ->
  Gamma ; ST' |- t \in T.
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    rewrite <- (extends_lookup _ _ ST')...
    apply T_Loc.
    eapply length_extends...
Qed.


Lemma store_well_typed_app : forall ST st t1 T1,
  store_well_typed ST st ->
  empty ; ST |- t1 \in T1 ->
  store_well_typed (ST ++ T1::nil) (st ++ t1::nil).
Proof with auto.
  intros.
  unfold store_well_typed in *.
  destruct H as [Hlen Hmatch].
  rewrite app_length, add_comm. simpl.
  rewrite app_length, add_comm. simpl.
  split...
  - (* types match. *)
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      apply lt_S_n in Hlt.
      rewrite !app_nth1...
      * apply store_weakening with ST. apply extends_app.
        apply Hmatch...
      * rewrite Hlen...
    + (* l = length st *)
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- Hlen.
      rewrite minus_diag. simpl.
      apply store_weakening with ST...
      { apply extends_app. }
      rewrite app_nth2; [|lia].
      rewrite minus_diag. simpl. assumption.
Qed.


Lemma nth_eq_last : forall A (l: list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.


 Theorem progress : forall ST t T st,
  empty ; ST |- t \in T ->
  store_well_typed ST st ->
  (value t \/ exists t' st', t / st --> t' / st').
Proof with eauto.
  intros ST t T st Ht HST. remember empty as Gamma.
  induction Ht; subst; try solve_by_invert...
  - (* T_App *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ (\ x0 : T0, t0) t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' t2 }>, st'...
  - (* T_Succ *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [ inversion Ht ].
      * (* t1 is a const *)
        exists <{ {S n} }>, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ succ t1' }>, st'...
  - (* T_Pred *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht ].
      * (* t1 is a const *)
        exists <{ {n - 1} }>, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ pred t1' }>, st'...
  - (* T_Mult *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t2 is a value *)
        inversion Ht2p; subst; try solve [inversion Ht2].
        exists <{ {n * n0} }>, st...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ n * t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' * t2 }>, st'...
  - (* T_If0 *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct n.
      * (* n = 0 *) exists t2, st...
      * (* n = S n' *) exists t3, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ if0 t1' then t2 else t3 }>, st'...
  - (* T_Ref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ref t1'}>, st'...
  - (* T_Deref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      eexists. eexists. apply ST_DerefLoc...
      inversion Ht; subst. inversion HST; subst.
      rewrite <- H...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ ! t1' }>, st'...
  - (* T_Assign *)
    right. destruct IHHt1 as [Ht1p|Ht1p]...
    + (* t1 is a value *)
      destruct IHHt2 as [Ht2p|Ht2p]...
      * (* t2 is a value *)
        inversion Ht1p; subst; try solve_by_invert.
        eexists. eexists. apply ST_Assign...
        inversion HST; subst. inversion Ht1; subst.
        rewrite H in H4...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ t1 := t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' := t2 }>, st'...
Qed.




Module ExampleVariables.
Open Scope string_scope.
Definition x := "x".
Definition y := "y".
Definition r := "r".
Definition s := "s".
End ExampleVariables.

Module RefsAndNontermination.
Import ExampleVariables.
Definition loop_fun :=
  <{ \x : Unit, (!r) unit }>.
Definition loop :=
  <{ (\r : Ref (Unit -> Unit), (( r := loop_fun ); ( (! r) unit ) )) (ref (\x : Unit, unit)) }> .

Lemma loop_typeable : exists T, empty; nil |- loop \in T.
Proof with eauto.
  eexists. unfold loop. unfold loop_fun.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
    eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.
    rewrite update_neq; [|intros; discriminate].
    rewrite update_eq. reflexivity. auto.
  eapply T_Assign.
    eapply T_Var. rewrite update_eq. reflexivity.
  eapply T_Abs.
    eapply T_App...
      eapply T_Deref. eapply T_Var. reflexivity.
Qed.


Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
  | sc_one : forall (x y : X),
                R x y -> step_closure R x y
  | sc_step : forall (x y z : X),
                R x y ->
                step_closure R y z ->
                step_closure R x z.
Definition multistep1 := (step_closure step).

Notation "t1 '/' st '-->+' t2 '/' st'" := (multistep1 (t1, st) (t2, st'))
                                          (at level 40, st at level 39, t2 at level 39).


Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; compute)];
            try solve [apply multi_refl]).



Lemma loop_steps_to_loop_fun :
  loop / nil -->*
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof.
  unfold loop.
  reduce.
Qed.


Lemma loop_fun_step_self :
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil -->+
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof with eauto.
  unfold loop_fun; simpl.
  eapply sc_step. apply ST_App1...
  eapply sc_one. compute. apply ST_AppAbs...
Qed.

(* TODO ex1: *)
Definition factorial : tm. Admitted.

Lemma factorial_type : empty; nil |- factorial \in (Nat -> Nat).
Proof with eauto. Admitted.

(* 
Lemma factorial_4 : exists st,
  <{ factorial 4 }> / nil -->* tm_const 24 / st.
Proof.
  eexists. unfold factorial. reduce.
Qed.
*)


(* TODO ex2:*)
(*
  Challenge problem: modify our formalization to include an account 
  of garbage collection, and prove that it satisfies whatever nice properties 
  you can think to prove about it.
*)
End RefsAndNontermination.
End STLCRef.



