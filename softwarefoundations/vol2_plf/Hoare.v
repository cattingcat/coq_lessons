Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.

From Coq Require Import Logic.FunctionalExtensionality.

Definition Assertion := state -> Prop.

Module ExAssertions.
  Definition assn1 : Assertion := fun st => st X <= st Y.
  Definition assn2 : Assertion := fun st => st X = 3 \/ st X <= st Y.
  Definition assn3 : Assertion := fun st => st Z * st Z <= st X /\ ~ (((S (st Z)) * (S (st Z))) <= st X).
  Definition assn4 : Assertion := fun st => st Z = max (st X) (st Y).
End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop := forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.
Notation "P <<->> Q" := (P ->> Q /\ Q ->> P) 
                        (at level 80) : hoare_spec_scope.

Definition Aexp : Type := state -> nat.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P"      := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q"   := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q"   := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q"   := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q"  := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b"    := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b"   := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b"   := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b"    := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b"   := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b"    := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b"    := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b"    := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b"    := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) := fun st => f (x st).
Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) := f (x st) (y st).

Module ExPrettyAssertions.
  Definition ex1 : Assertion := X = 3.
  Definition ex2 : Assertion := True.
  Definition ex3 : Assertion := False.
  Definition assn1 : Assertion := X <= Y.
  Definition assn2 : Assertion := X = 3 \/ X <= Y.
  Definition assn3 : Assertion := Z * Z <= X /\ ~ (((ap S Z) * (ap S Z)) <= X).
  Definition assn4 : Assertion := Z = ap2 max X Y.
End ExPrettyAssertions.


Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

Check ({{True}} X := 0 {{True}}).


Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) -> {{P}} c {{Q}}.
Proof.
  intros P Q c H.
  unfold hoare_triple.
  intros st st' cmd Hp.
  apply  (H st').
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) -> {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple. intros st st' cmd Hp.
  exfalso.
  apply (H st).
  assumption.
Qed.



Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) => P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
                           (at level 10, X at next level, a custom com).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof. intros Q X a. unfold hoare_triple. intros st st' cmd Hq.
  inversion cmd. subst.
  unfold assn_sub in Hq. apply Hq. Qed.

Example assn_sub_example :
  {{(X < 5) [X |-> X + 1]}} X := X + 1 {{X < 5}}.
Proof.
  apply hoare_asgn. Qed.

Example hoare_asgn_examples1 :
  exists P, {{ P }} X := 2 * X {{ X <= 10 }}.
Proof.
  exists (assert (X <= 5)).
  unfold hoare_triple. intros st st' cmd Hq.
  simpl in *.
  inversion cmd. subst. unfold t_update.
  simpl. lia.
Qed.

Example hoare_asgn_examples2 :
  exists P, {{ P }} X := 3 {{ 0 <= X /\ X <= 5 }}.
Proof.
  exists True.
  unfold hoare_triple. intros st st' cmd Hq.
  simpl.
  inversion cmd; subst; simpl in *.
  unfold t_update; simpl. lia.
Qed.

Example vice_versa_wrong: 
  exists a, ~ ({{ True }} X := a {{ X = a }}).
Proof.
  exists (<{ X + 1 }>).
  unfold hoare_triple.
  intros H. simpl in H.
  assert (G: 1 = 1 + 1). {
    apply (H (X !-> 0) (X !-> 1; X !-> 0)).
    apply E_Asgn. simpl.
    reflexivity.
    apply I.
  }
  discriminate G.
Qed.

Lemma qwe: forall st X (n: nat),
  (X !-> st X; X !-> n; st) = st.
Proof.
  intros st X n.
  unfold t_update. unfold eqb_string.
  apply functional_extensionality.
  intros x.
  destruct (string_dec X x) as [E | E].
  - rewrite E. reflexivity.
  - reflexivity.
Qed.

Theorem hoare_asgn_fwd : forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  unfold hoare_triple.
  intros m a P st st' comm [Hpst Estx].
  inversion comm; subst.
  rewrite qwe. unfold t_update; simpl.
  split.
  - assumption.
  - reflexivity.
Qed.

Lemma asd: forall X a st st',
  st =[ X := a ]=> st' -> exists m, (X !-> m; st') = st.
Proof.
  intros X a st st' H.
  inversion H; subst; simpl in *.
  exists (st X).
  apply qwe.
Qed.


Theorem hoare_asgn_fwd_exists : forall a P,
  {{fun st => P st}}
    X := a
  {{fun st => exists m, P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  unfold hoare_triple.
  intros a P st st' comm Hp.
  inversion comm; subst; simpl in *.
  destruct (asd _ _ _ _ comm) as [m' Hst].
  exists m'.
  rewrite Hst.
  unfold t_update; simpl.
  split.
  - assumption.
  - reflexivity.
Qed.



Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->  P ->> P'  -> {{P}} c {{Q}}.
Proof. intros P P' Q c H1 H2.
  unfold hoare_triple in *.
  intros st st' c' Hpst.
  apply (H1 st st' c' (H2 st Hpst)).
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->  Q' ->> Q  -> {{P}} c {{Q}}.
Proof.
  intros P Q Q' c H1 H2.
  unfold hoare_triple in *.
  intros st st' c' Hpst.
  apply H2.
  apply (H1 st st' c' Hpst).
Qed.


Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre with (P' := (X = 1) [X |-> 1]).
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

Example assn_sub_example2 :
  {{X < 4}} X := X + 1 {{X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre with (P' := (X < 5) [X |-> X + 1]).
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st H. simpl in *. lia.
Qed.


Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->  P ->> P' -> Q' ->> Q ->  {{P}} c {{Q}}.
Proof. intros.
  apply (hoare_consequence_pre) with (P' := P').
    - apply (hoare_consequence_post) with (Q' := Q').
      + apply H.
      + apply H1.
    - apply H0.
Qed.


(* Hints for auto tactic *)
Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->   P ->> P' ->  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.


Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->   P ->> P' ->  {{P}} c {{Q}}.
Proof. eauto. Qed.


Ltac assn_auto :=
  try auto; (* as in example 1, above *)
  try (unfold "->>", assn_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assn_sub_ex1' :
  {{ X <= 5 }}  X := 2 * X  {{ X <= 10 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

Example assn_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}  X := 3  {{ 0 <= X /\ X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.




Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof. unfold hoare_triple. intros P st st' Hcomm Hpst.
  inversion Hcomm; subst. assumption.
Qed.


Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} -> {{P}} c1 {{Q}} -> {{P}} c1; c2 {{R}}.
Proof. intros P Q R c1 c2 H1 H2. unfold hoare_triple in *. intros st st' Hcomm Hpst.
  inversion Hcomm; subst.
  eauto.
  (* eapply H1.
  apply H6.
  eapply H2.
  apply H3.
  apply Hpst. *)
Qed.

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
    {{a = n}}
  X := a;
  skip
    {{X = n}}.
Proof.
  intros a n. 
  eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

Example tst_seq_1 : 
    {{ True }}
  X := 1;
  Y := 2
    {{X = 1 /\ Y = 2}}.
Proof.
  eapply hoare_seq with (Q := assert (X = 1)).
  - eapply hoare_consequence_pre with (P' := assert (X = 1 /\ Y = 2) [Y |-> 2]).
    + apply hoare_asgn.
    + assn_auto.
  - apply hoare_consequence_pre with (P' := (X = 1) [X |-> 1]).
    + apply hoare_asgn.
    + assn_auto.
Qed.


Definition swap_program : com :=
  <{ Z := X; X := Y; Y := Z }>.

Theorem swap_exercise :
  {{X <= Y}}
  swap_program
  {{Y <= X}}.
Proof.
  eapply hoare_seq with (Q := assert (Z <= Y)).
  - eapply hoare_seq with (Q := assert (Z <= X)).
    + apply hoare_consequence_pre with (P' := (Y <= X) [Y |-> Z]).
      * apply hoare_asgn.
      * assn_auto.
    + apply hoare_consequence_pre with (P' := (Z <= X) [X |-> Y]).
      * apply hoare_asgn.
      * assn_auto.
  - apply hoare_consequence_pre with (P' := (Z <= Y) [Z |-> X]).
    * apply hoare_asgn.
    * assn_auto.
Qed.


Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  unfold hoare_triple.
  intros H.
  specialize H with (a := X) (n := 0).
  simpl in *.
  assert (G: (X !-> 0) =[ X := 3; Y := X ]=> (Y !-> 3; X !-> 3; X !-> 0)). {
    eapply (E_Seq).
    apply E_Asgn.
    - simpl. reflexivity.
    - eapply E_Asgn.
      simpl. reflexivity.
  }
  assert (G': 3 = 0). {
    apply (H _ _ G).
    reflexivity.
  }
  discriminate G'.
Qed.



Definition bassn b : Assertion := fun st => (beval st b = true).
Coercion bassn : bexp >-> Assertion.
Arguments bassn /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~((bassn b) st).
Proof. intros b st H. unfold not, bassn. intro H'. 
  congruence. (* H and H' *) Qed.

Hint Resolve bexp_eval_false : core.


Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof. intros P Q b c1 c2. unfold hoare_triple.
  intros H1 H2 st st' Hif Hpst.
  inversion Hif; subst.
  - (* if true *)
    apply (H1 st st' H7). split; assumption.
  - (* if false *)
    apply (H2 st st' H7). split.
    + apply Hpst.
    + unfold not. simpl. intro Hcontra. congruence.
Qed.

Example if_example :
    {{True}}
  if (X = 0)
    then Y := 2
    else Y := X + 1
  end
    {{X <= Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto. (* no progress *)
      unfold "->>", assn_sub, t_update, bassn.
      simpl. intros st [_ H].
      apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

Ltac assn_auto' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

Example if_example''' :
  {{True}}
  if X = 0
    then Y := 2
    else Y := X + 1
  end
  {{X <= Y}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assn_auto'.
Qed.


Ltac assn_auto'' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *; (* for inequalities *)
  auto; try lia.

Theorem if_minus_plus :
  {{True}}
  if (X <= Y)
    then Z := Y - X
    else Y := X + Z
  end
  {{Y = X + Z}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto''.
Qed.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* We proceed by induction on Heval, because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just c. The
     remember is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the induction. By using inversion
     we clear away all the cases except those involving while. *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.




Module RepeatExercise.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'repeat' e 'until' b 'end'" :=
     (CRepeat e b)
        (in custom com at level 0, e custom com at level 99, b custom com at level 99).
Notation "'skip'" :=
     (CSkip) (in custom com at level 0).
Notation "x := y" :=
     (CAsgn x y)
        (in custom com at level 0, x constr at level 0, y at level 85, no associativity).
Notation "x ; y" :=
     (CSeq x y)
        (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
     (CIf x y z)
        (in custom com at level 89, x at level 99, y at level 99, z at level 99).
Notation "'while' b 'do' e 'end'" :=
     (CWhile b e)
        (in custom com at level 89, b at level 99, e at level 99).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_RepeatTrue : forall b st st' c,
      st =[ c ]=> st' ->
      beval st' b = true ->
      st =[ repeat c until b end ]=> st'
  | E_RepeatFalse : forall st st' st'' b c,
      st =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st =[ repeat c until b end ]=> st''

where "st '=[' c ']=>' st'" := (ceval st c st').

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c custom com at level 99).


Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.
Theorem ex1_repeat_works : empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
  apply E_RepeatTrue.
  - apply (E_Seq) with (st' := (X !-> 1)).
    + constructor. reflexivity.
    + constructor. reflexivity.
  - reflexivity.
Qed.

Theorem hoare_repeat : forall P (b:bexp) c,
  {{P}} c {{P}} ->
  {{P}} repeat c until b end {{P /\ b}}.
Proof.
  intros P b c Hc st st' Hrepeat Hpst.
  remember <{ repeat c until b end }> as r eqn:Er.
  induction Hrepeat; 
    try (discriminate Er);
    try (injection Er as Erc Erb; subst).
  - clear IHHrepeat. split.
    + apply (Hc st st' Hrepeat Hpst).
    + simpl. assumption.
  - apply IHHrepeat2.
    + reflexivity.
    + apply (Hc st st' Hrepeat1 Hpst).
Qed.

Search (?a /\ ?b <-> ?b /\ ?a).


Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->   P ->> P' ->  {{P}} c {{Q}}.
Proof. Admitted.

Example tst:
 {{ X > 0 }}
  repeat
    Y := X;
    X := X - 1
  until X = 0 end
  {{ X = 0 /\ Y > 0 }}.
Proof. Admitted.
End RepeatExercise.




Module Himp.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'havoc' l" := (CHavoc l)
                        (in custom com at level 60, l constr at level 0).
Notation "'skip'" := CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
          (in custom com at level 0, x constr at level 0, y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
          (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
          (in custom com at level 89, x at level 99, y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
          (in custom com at level 89, x at level 99, y at level 99).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_Havoc : forall st X n,
      st =[ havoc X ]=> (X !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.
Hint Unfold hoare_triple : core.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c custom com at level 99): hoare_spec_scope.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->  P ->> P' ->  {{P}} c {{Q}}.
Proof. eauto. Qed.


Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop :=
  forall n, Q (X !-> n; st).

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} havoc X {{ Q }}.
Proof.
  intros Q X st st' Hhavok Hqpre.
  inversion Hhavok; subst.
  apply Hqpre.
Qed.

Theorem havoc_post : forall (P : Assertion) (X : string),
  {{ P }} havoc X {{ fun st => exists (n:nat), P [X |-> n] st }}.
Proof.
  intros P X. eapply hoare_consequence_pre.
  - apply hoare_havoc.
  - intros st Hpst npre.
    exists (st X).
    unfold assn_sub. simpl.
    assert (G: (X !-> st X; X !-> npre; st) = st). {
      apply functional_extensionality.
      intro x. unfold t_update, eqb_string.
      destruct (string_dec X x) as [ H | H ]; subst; reflexivity.
    }
    rewrite G. assumption.
Qed.

End Himp.
