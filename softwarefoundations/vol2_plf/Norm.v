Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Constructors multi : core.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
    (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
    (* booleans *)
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
    (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" := (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                           t custom stlc at level 99,
                           y custom stlc at level 99,
                           left associativity).
Coercion tm_var : string >-> tm.
Notation "{ x }" := x (in custom stlc at level 1, x constr).
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" := (tm_if x y z) (in custom stlc at level 89,
                                        x custom stlc at level 99,
                                        y custom stlc at level 99,
                                        z custom stlc at level 99,
                                        left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).
Notation "X * Y" := (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
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
  | <{ \ y : T, t1 }> =>
      if eqb_string x y then t else <{ \y:T, [x:=s] t1 }>
  | <{t1 t2}> =>
      <{ ([x:=s]t1) ([x:=s]t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{(t1, t2)}> =>
      <{( ([x:=s] t1), ([x:=s] t2) )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
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
        <{ (t1,t2) }> --> <{ (t1' , t2) }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.fst }> --> <{ t0'.fst }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).fst }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.snd }> --> <{ t0'.snd }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).snd }> --> v2
where "t '-->' t'" := (step t t').
Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof with eauto.
  intros t H; induction H; intros [t' ST]; inversion ST...
Qed.


Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc at level 0).
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
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |- t0 \in (T1 * T2) ->
      Gamma |- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |- t0 \in (T1 * T2) ->
      Gamma |- t0.snd \in T2
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

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
Proof with eauto.
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


Theorem preservation : forall t t' T,
   empty |- t \in T ->
   t --> t' ->
   empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
    intros t' HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
  - (* T_Fst *)
    inversion HT...
  - (* T_Snd *)
    inversion HT...
Qed.

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
  (* booleans *)
  | afi_test0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ (t1 , t2) }>
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.fst }>
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.snd }>.
Hint Constructors appears_free_in : core.


Definition closed (t:tm) :=  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in S.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; eauto 12.
  - (* T_Var *)
    apply T_Var. rewrite <- H0; auto.
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... *)
    destruct (eqb_stringP x x1); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      auto.
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
Qed.

Corollary typable_empty__closed : forall t T,
    empty |- t \in T ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C. Qed.

Lemma step_deterministic :   deterministic step.
Proof with eauto.
   unfold deterministic.
   intros t t' t'' E1 E2.
   generalize dependent t''.
   induction E1; intros t'' E2; inversion E2; subst; clear E2...
  (* ST_AppAbs *)
   - inversion H3.
   - exfalso; apply value__normal in H...
   (* ST_App1 *)
   - inversion E1.
   - f_equal...
   - exfalso; apply value__normal in H1...
   (* ST_App2 *)
   - exfalso; apply value__normal in H3...
   - exfalso; apply value__normal in H...
   - f_equal...
   - (* ST_IfTrue *)
       inversion H3.
   - (* ST_IfFalse *)
       inversion H3.
   (* ST_If *)
   - inversion E1.
   - inversion E1.
   - f_equal...
   (* ST_Pair1 *)
   - f_equal...
   - exfalso; apply value__normal in H1...
   (* ST_Pair2 *)
   - exfalso; apply value__normal in H...
   - f_equal...
   (* ST_Fst1 *)
   - f_equal...
   - exfalso.
     inversion E1; subst.
     + apply value__normal in H0...
     + apply value__normal in H1...
   (* ST_FstPair *)
   - exfalso.
     inversion H2; subst.
     + apply value__normal in H...
     + apply value__normal in H0...
   (* ST_Snd1 *)
   - f_equal...
   - exfalso.
     inversion E1; subst.
     + apply value__normal in H0...
     + apply value__normal in H1...
   (* ST_SndPair *)
   - exfalso.
     inversion H2; subst.
     + apply value__normal in H...
     + apply value__normal in H0...
Qed.


Definition halts (t:tm) : Prop := exists t', t -->* t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  - apply multi_refl.
  - assumption.
Qed.

(*
  Inductive R : ty -> tm -> Prop :=
      | R_bool : forall b t, 
                      empty |- t \in Bool ->
                      halts t ->
                      R Bool t
      | R_arrow : forall T1 T2 t, 
                      empty |- t \in (Arrow T1 T2) ->
                      halts t ->
                      (forall s, R T1 s -> R T2 (app t s)) ->
                      R (Arrow T1 T2) t.
*)

Fixpoint R (T:ty) (t:tm) : Prop :=
  empty |- t \in T /\ halts t /\
  (match T with
   | <{ Bool }> => True
   | <{ T1 -> T2 }> => (forall s, R T1 s -> R T2 <{t s}> )
   | <{ T1 * T2 }> => True
   end).

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [_ [H _]]; assumption.
Qed.


Lemma R_typable_empty : forall {T} {t}, R T t -> empty |- t \in T.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [H _]; assumption.
Qed.


Lemma step_preserves_halting :
  forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST. unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  destruct STM.
   + exfalso; apply value__normal in V; eauto.
   + rewrite (step_deterministic _ _ _ ST H). exists z. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
Qed.

Lemma step_preserves_R : forall T t t', (t --> t') -> (R T t -> R T t').
Proof.
 induction T; intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
  (* Bool *)
  - split. eapply preservation; eauto.
    split. apply (step_preserves_halting _ _ E); eauto.
    auto.
  (* Arrow *)
  - split. eapply preservation; eauto.
    split. apply (step_preserves_halting _ _ E); eauto.
    intros.
    eapply IHT2.
    apply ST_App1. apply E.
    apply RRt; auto.
  - (* Pair *)
    split. eapply preservation; eauto.
    split. apply (step_preserves_halting _ _ E); eauto.
    auto. (* Probably incorrect *)
Qed.

Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> (R T t -> R T t').
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.

Lemma step_preserves_R' : forall T t t',
  empty |- t \in T -> (t --> t') -> R T t' -> R T t.
Proof.
  intros T. induction T; intros t t' Ht Hp Rt'; unfold R in Rt'; unfold R.
  - destruct Rt' as [Ht' [Hhaltt' _]].
    split. assumption.
    split. rewrite (step_preserves_halting t t' Hp). assumption.
    auto.
  - fold R. fold R in Rt'.
    destruct Rt' as [Ht' [Hhaltt' Hf]].
    split. apply Ht.
    split. rewrite (step_preserves_halting t t' Hp). assumption.
    intros s Rs.
    apply IHT2 with <{ t' s }>.
    + eapply T_App. apply Ht. apply (R_typable_empty Rs).
    + constructor. assumption.
    + apply Hf. assumption.
  - destruct Rt' as [Ht' [Hhaltt' _]].
    split. assumption.
    split. rewrite (step_preserves_halting t t' Hp). assumption.
    auto.
Qed.

Lemma multistep_preserves_R' : forall T t t',
  empty |- t \in T -> (t -->* t') -> (R T t' -> R T t).
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'. assumption. apply H. apply IHSTM.
    eapply preservation; eauto. auto.
Qed.



Definition env := list (string * tm).

Fixpoint msubst (ss: env) (t: tm) : tm :=
  match ss with
  | nil           => t
  | ((x, s)::ss') => msubst ss' <{ [x:=s]t }>
  end.


Definition tass := list (string * ty).

Fixpoint mupdate (Gamma: context) (xts: tass) :=
  match xts with
  | nil             => Gamma
  | ((x, v)::xts')  => update (mupdate Gamma xts') x v
  end.


Fixpoint lookup {X:Set} (k: string) (l: list (string * X)) : option X :=
  match l with
    | nil           => None
    | (j, x) :: l'  =>
      if eqb_string j k then Some x else lookup k l'
  end.

Fixpoint drop {X:Set} (n: string) (nxs: list (string * X)) : list (string * X) :=
  match nxs with
    | nil             => nil
    | ((n', x)::nxs') =>
        if eqb_string n' n 
        then drop n nxs'
        else (n', x) :: (drop n nxs')
  end.


Inductive instantiation : tass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T v c e,
    value v  ->  R T v ->
    instantiation c e ->
    instantiation ((x,T)::c) ((x,v)::e).


Lemma vacuous_substitution : forall t x,
     ~(appears_free_in x t) ->
     forall t', <{ [x:=t']t }> = t.
Proof with eauto.
  intros t.
  induction t; intros x Hnot_app t'.
  - unfold subst.
    unfold eqb_string.
    destruct (string_dec x s) as [H | H]; subst.
    + exfalso. apply Hnot_app...
    + reflexivity.
  - simpl.
    assert (G2: ~ appears_free_in x t2). { intro H. apply Hnot_app. apply afi_app2. assumption. }
    assert (G1: ~ appears_free_in x t1). { intro H. apply Hnot_app. apply afi_app1. assumption. }
    rewrite (IHt1 x G1).
    rewrite (IHt2 x G2).
    reflexivity.
  - simpl.
    unfold eqb_string.
    destruct (string_dec x s) as [H | H]; subst.
    + reflexivity.
    + assert (G: ~ appears_free_in x t0). { intro H'. apply Hnot_app. apply afi_abs... }
      rewrite (IHt x G)...
  - simpl...
  - simpl...
  - simpl.
    assert (G: ~ appears_free_in x t1). { intro H'. apply Hnot_app. apply afi_test0... }
    assert (G1: ~ appears_free_in x t2). { intro H'. apply Hnot_app. apply afi_test1... }
    assert (G2: ~ appears_free_in x t3). { intro H'. apply Hnot_app. apply afi_test2... }
    rewrite (IHt1 x G).
    rewrite (IHt2 x G1).
    rewrite (IHt3 x G2).
    reflexivity.
  - simpl.
    assert (G1: ~ appears_free_in x t1). { intro H'. apply Hnot_app. apply afi_pair1... }
    assert (G2: ~ appears_free_in x t2). { intro H'. apply Hnot_app. apply afi_pair2... }
    rewrite (IHt1 x G1).
    rewrite (IHt2 x G2).
    reflexivity.
  - simpl.
    assert (G: ~ appears_free_in x t). { intro H'. apply Hnot_app. apply afi_fst... }
    rewrite (IHt x G)...
  - simpl.
    assert (G: ~ appears_free_in x t). { intro H'. apply Hnot_app. apply afi_snd... }
    rewrite (IHt x G)...
Qed.


Lemma subst_closed: forall t,
     closed t -> forall x t', <{ [x:=t']t }> = t.
Proof.
  intros. apply vacuous_substitution. apply H. Qed.

Lemma subst_not_afi : forall t x v,
    closed v  ->  ~ appears_free_in x <{ [x:=v]t }>.
Proof with eauto. (* rather slow this way *)
  unfold closed, not.
  induction t; intros x v P A; simpl in A.
    - (* var *)
     destruct (eqb_stringP x s)...
     inversion A; subst. auto.
    - (* app *)
     inversion A; subst...
    - (* abs *)
     destruct (eqb_stringP x s)...
     + inversion A; subst...
     + inversion A; subst...
    - (* tru *)
     inversion A.
    - (* fls *)
     inversion A.
    - (* test *)
     inversion A; subst...
    - (* pair *)
     inversion A; subst...
    - (* fst *)
     inversion A; subst...
    - (* snd *)
     inversion A; subst...
Qed.

Lemma duplicate_subst : forall t' x t v,
  closed v  ->  <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi. assumption.
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof with eauto.
 induction t; intros; simpl.
  - (* var *)
   destruct (eqb_stringP x s); destruct (eqb_stringP x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite <- eqb_string_refl. apply subst_closed...
   + subst. simpl. rewrite <- eqb_string_refl. rewrite subst_closed...
   + simpl. rewrite false_eqb_string... rewrite false_eqb_string...
  - (* app *)
    rewrite IHt1...
    rewrite IHt2...
  - (* abs *)
    destruct (eqb_stringP x s); destruct (eqb_stringP x1 s).
    + subst. simpl. rewrite <- eqb_string_refl...
    + subst. simpl. rewrite false_eqb_string... rewrite <- eqb_string_refl...
    + subst. simpl. rewrite <- eqb_string_refl... rewrite false_eqb_string...
    + subst. simpl. rewrite false_eqb_string... rewrite false_eqb_string...
      rewrite IHt...
  - reflexivity.
  - reflexivity.
  - rewrite IHt1...
    rewrite IHt2...
    rewrite IHt3...
  - rewrite IHt1...
    rewrite IHt2...
  - rewrite IHt...
  - rewrite IHt...
Qed.




Lemma msubst_closed: forall t, closed t  ->  forall ss, msubst ss t = t.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.

Fixpoint closed_env (env:env): Prop :=
  match env with
  | nil         => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

Lemma subst_msubst: forall env x v t, closed v  ->  closed_env env ->
    msubst env <{ [x:=v]t }> = <{ [x:=v] { msubst (drop x env) t } }> .
Proof.
  induction env0; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (eqb_stringP s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.

Lemma msubst_var: forall ss x, closed_env ss ->
   msubst ss (tm_var x) =
   match lookup x ss with
   | Some t => t
   | None   => tm_var x
  end.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
     simpl. destruct (eqb_string s x).
      apply msubst_closed. inversion H; auto.
      apply IHss. inversion H; auto.
Qed.

Lemma msubst_abs: forall ss x T t,
  msubst ss <{ \ x : T, t }> = <{ \x : T, {msubst (drop x ss) t} }>.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (eqb_string s x); simpl; auto.
Qed.

Lemma msubst_app : forall ss t1 t2,
    msubst ss <{ t1 t2 }> = <{ {msubst ss t1} ({msubst ss t2}) }>.
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_true : forall ss,
    msubst ss <{ true }> = <{ true }>.
Proof.
 induction ss; intros.
 - reflexivity.
 - simpl. rewrite IHss.
   destruct a. reflexivity.
Qed.

Lemma msubst_false : forall ss,
    msubst ss <{ false }> = <{ false }>.
Proof.
 induction ss; intros.
 - reflexivity.
 - simpl. rewrite IHss.
   destruct a. reflexivity.
Qed.

Lemma mupdate_lookup : forall (c : tass) (x:string),
    lookup x c = (mupdate empty c) x.
Proof.
  induction c; intros.
    auto.
    destruct a. unfold lookup, mupdate, update, t_update. destruct (eqb_string s x); auto.
Qed.

Lemma mupdate_drop : forall (c: tass) Gamma x x',
      mupdate Gamma (drop x c) x'
        = if eqb_string x x' then Gamma x' else mupdate Gamma c x'.
Proof.
  induction c; intros.
  - destruct (eqb_stringP x x'); auto.
  - destruct a. simpl.
    destruct (eqb_stringP s x).
    + subst. rewrite IHc.
      unfold update, t_update. destruct (eqb_stringP x x'); auto.
    + simpl. unfold update, t_update. destruct (eqb_stringP s x'); auto.
      subst. rewrite false_eqb_string; congruence.
Qed.


Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {T},
      lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
  intros c e V. induction V; intros x0 T0 C.
    solve_by_invert.
    simpl in *.
    destruct (eqb_string x x0); eauto.
Qed.

Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
Proof.
  intros c e V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    split; [|assumption].
    eapply typable_empty__closed. eapply R_typable_empty. eauto.
Qed.

Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
Proof.
  intros c e V. induction V; intros x' t' T' G E.
    solve_by_invert.
    unfold lookup in *. destruct (eqb_string x x').
      inversion G; inversion E; subst. auto.
      eauto.
Qed.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V. induction V.
    intros. simpl. constructor.
    intros. unfold drop.
    destruct (eqb_string x x0); auto. constructor; eauto.
Qed.


Lemma multistep_App2 : forall v t t',
  value v -> 
  (t -->* t') -> 
  <{ v t }> -->* <{ v t' }>.
Proof.
  intros v t t' V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2; eauto. auto.
Qed.



 Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, (mupdate Gamma c) |- t \in S ->
     Gamma |- { (msubst e t) } \in S.
Proof.
  induction 1; intros.
    simpl in H. simpl. auto.
    simpl in H2. simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.


Lemma msubst_R : forall c env t T,
    (mupdate empty c) |- t \in T ->
    instantiation c env ->
    R T (msubst env t).
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c). {
    intros. rewrite HeqGamma. rewrite mupdate_lookup. auto. }
  clear HeqGamma.
  generalize dependent c.
  induction HT; intros.
  - (* T_Var *)
   rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubst_var. rewrite P. auto. eapply instantiation_env_closed; eauto.
  - (* T_Abs *)
    rewrite msubst_abs.
    (* We'll need variants of the following fact several times, so its simplest to
       establish it just once. *)
    assert (WT : empty |- \x : T2, {msubst (drop x env0) t1 } \in (T2 -> T1) ).
    { eapply T_Abs. eapply msubst_preserves_typing.
      { eapply instantiation_drop; eauto. }
      eapply context_invariance.
      { apply HT. }
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_stringP x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl. rewrite false_eqb_string; auto.
        simpl. destruct a. unfold update, t_update.
        destruct (eqb_string s x0); auto. }
    unfold R. fold R. split.
       auto.
     split. apply value_halts. apply v_abs.
     intros.
     destruct (R_halts H0) as [v [P Q]].
     pose proof (multistep_preserves_R _ _ _ P H0).
     apply multistep_preserves_R' with (msubst ((x,v)::env0) t1).
       eapply T_App. eauto.
       apply R_typable_empty; auto.
       eapply multi_trans. eapply multistep_App2; eauto.
       eapply multi_R.
       simpl. rewrite subst_msubst.
       eapply ST_AppAbs; eauto.
       eapply typable_empty__closed.
       apply (R_typable_empty H1).
       eapply instantiation_env_closed; eauto.
       eapply (IHHT ((x,T2)::c)).
          intros. unfold update, t_update, lookup. destruct (eqb_string x x0); auto.
       constructor; auto.
  - (* T_App *)
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c H env0 V) as P2. fold R in P1. auto.
  - (* true *) simpl. auto.
    rewrite msubst_true.
    split. constructor.
    split. unfold halts. exists <{ true }>. auto.
    auto.
  - (* false *) simpl. auto.
    rewrite msubst_false.
    split. constructor.
    split. unfold halts. exists <{ false }>. auto.
    auto.
  - (* if *)
    simpl.
  (* TODO *) Admitted.

Theorem normalization : forall t T, empty |- t \in T  ->  halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.

