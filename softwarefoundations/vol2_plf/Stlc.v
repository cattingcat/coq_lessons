Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Module STLC.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

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

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Notation idB :=
  <{ \x:Bool, x }>.
Notation idBB :=
  <{ \x:Bool->Bool, x }>.
Notation idBBBB :=
  <{\x:((Bool->Bool)->(Bool->Bool)), x}>.
Notation k := <{\x:Bool, \y:Bool, x}>.
Notation notB := <{\x:Bool, if x then false else true}>.



Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{ \x:T2, t1 }>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> => <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Check <{[x:=true] x}>.

(*
Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.
*)
Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tm_var x) s
  | s_var2 : forall y,
      ~(x = y) ->
      substi s x (tm_var y) (tm_var y)
  | s_app : forall l r l' r',
      substi s x l l' ->
      substi s x r r' ->
      substi s x (tm_app l r) (tm_app l' r')
  | s_abs_bound : forall t b,
      substi s x (tm_abs x t b) (tm_abs x t b)
  | s_abs_free : forall a t b b',
      ~(x = a) ->
      substi s x b b' ->
      substi s x (tm_abs a t b) (tm_abs a t b')
  | s_true :
      substi s x tm_true tm_true
  | s_false :
      substi s x tm_false tm_false
  | s_if : forall b b' l l' r r',
      substi s x b b' ->
      substi s x l l' ->
      substi s x r r' ->
      substi s x (tm_if b l r) (tm_if b' l' r')
.
Hint Constructors substi : core.

Search (eqb_string ?s ?s = true).


Theorem substi_correct_fw : forall s x t t',
  <{ [x:=s]t }> = t'  ->  substi s x t t'.
Proof.
  intros s x t.
  induction t; intros t' H; simpl in H.
  + (*var*) unfold eqb_string in H.
    destruct (string_dec x s0); subst.
    * constructor.
    * constructor. apply n.
  + (*app*) 
    subst.
    eapply s_app.
    apply IHt1. reflexivity.
    apply IHt2. reflexivity.
  + (*abs*) unfold eqb_string in H.
    destruct (string_dec x s0); subst.
    * constructor.
    * constructor.
      assumption.
      apply IHt. reflexivity.
  + (*true*)  subst. constructor.
  + (*false*) subst. constructor.
  + (*if*) subst. constructor; auto.
Qed.

Theorem substi_correct_bw : forall s x t t',
  substi s x t t'  ->  <{ [x:=s]t }> = t'.
Proof.
  intros s x t t' H.
  induction H.
  - (*var*) simpl. unfold eqb_string.
    destruct (string_dec x x); subst.
    + reflexivity.
    + exfalso. apply n. reflexivity.
  - (*var not eq*) 
    simpl. unfold eqb_string.
    destruct (string_dec x y0); subst.
    + exfalso. apply H. reflexivity.
    + reflexivity.
  - (*app*)
    subst. simpl. reflexivity.
  - (*abs bound*) simpl. unfold eqb_string.
    destruct (string_dec x x); subst.
    + reflexivity.
    + exfalso. apply n. reflexivity.
  - (*abs free*) simpl. unfold eqb_string.
    destruct (string_dec x a); subst.
    + exfalso. apply H. reflexivity.
    + reflexivity.
  - (*true*) reflexivity.
  - (*false*) reflexivity.
  - (*if*) simpl. subst. reflexivity.
Qed.


Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t'  <->  substi s x t t'.
Proof.
  intros s x t t'.
  split.
  - apply substi_correct_fw.
  - apply substi_correct_bw.
Qed.


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
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl. Qed.

Lemma step_example5 :
       <{idBBBB idBB idB}>  -->* idB.
Proof.
    eapply multi_step.
      apply ST_App1.
      - apply ST_AppAbs. constructor.
      - simpl. 
        eapply multi_step. apply ST_AppAbs.
        + constructor.
        + simpl.
          apply multi_refl. Qed.

Lemma step_example5_with_normalize :
       <{idBBBB idBB idB}>  -->* idB.
Proof. normalize. Qed.





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
  | T_True : forall Gamma,
       Gamma |- true \in Bool
  | T_False : forall Gamma,
       Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Example typing_example_1 :
  empty |- \x:Bool, x \in (Bool -> Bool).
Proof.
  apply T_Abs. apply T_Var. reflexivity. Qed.

Example typing_example_2_full :
  empty |-
    \x:Bool,
       \y:Bool->Bool,
          (y (y x)) \in
    (Bool -> (Bool -> Bool) -> Bool).
Proof.
  apply T_Abs.
  apply T_Abs.
  apply T_App with (T2 := <{ Bool }> ).
  - apply T_Var. unfold "|->", t_update. simpl. reflexivity.
  - apply T_App with (T2 := <{ Bool }> ).
    + apply T_Var. unfold "|->", t_update. simpl. reflexivity.
    + apply T_Var. unfold "|->", t_update. simpl. reflexivity.
Qed.


Example typing_example_3 :
  exists T,
    empty |-
      \x:Bool->Bool,
         \y:Bool->Bool,
            \z:Bool,
               (y (x z)) \in
      T.
Proof.
  eexists.
  apply T_Abs.
  apply T_Abs.
  apply T_Abs.
  apply T_App with (T2 := <{ Bool }> ).
  - apply T_Var. unfold "|->", t_update. simpl. reflexivity.
  - apply T_App with (T2 := <{ Bool }> ).
    + apply T_Var. unfold "|->", t_update. simpl. reflexivity.
    + apply T_Var. unfold "|->", t_update. simpl. reflexivity.
Qed.

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        \x:Bool,
            \y:Bool,
               (x y) \in
        T.
Proof.
  intros Hc. destruct Hc as [T Hc].
  (* The clear tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5 H4.
  inversion H2; subst; clear H2.
  discriminate H1.
Qed.



Lemma qwe: forall t1 t2, <{t1 -> t2 }> = t1 -> False.
Proof.
  intros t1.
  induction t1; intros t2 H.
  - discriminate H.
  - injection H as H.
    apply (IHt1_1 _ H).
Qed.

Example typing_nonexample_3 :
  ~ (exists S T,
        empty |-
          \x:S, x x \in T).
Proof.
  intros [ S [ T HT ]].
  inversion HT; subst.
  inversion H4; subst.
  inversion H2; subst.
  inversion H5; subst.
  injection H1 as H1.
  injection H3 as H3.
  rewrite H1 in H3.
  apply (qwe T2 T1 H3).
Qed.

End STLC.
