Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Import Imp.
From PLF Require Import Hoare.

From Coq Require Import Logic.FunctionalExtensionality.

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
         (in custom com at level 0, x custom com at level 99).
Notation "'skip'" :=
         CSkip 
         (in custom com at level 0).
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

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr, st' constr at next level).
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
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ if1 b then c end ]=> st'
  | E_If1False : forall st b c,
      beval st b = false ->
      st =[ if1 b then c end ]=> st
  where "st =[ c ]=> st'" := (ceval c st st').

Hint Constructors ceval : core.

Example if1true_test : empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. eauto. Qed.

Example if1false_test : (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. eauto. Qed.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.
Hint Unfold hoare_triple : core.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                (at level 90, c custom com at level 99)
                                : hoare_spec_scope.

Theorem hoare_if1: forall P Q (b:bexp) c,
  {{ P /\ b }} c {{Q}} ->
  (P /\ ~b)%assertion ->> Q ->
  {{P}} if1 b then c end {{Q}}.
Proof. unfold hoare_triple. intros P Q b c H1 H2 st st' Hcom Hpst.
  inversion Hcom; subst.
  - apply (H1 st st' H6); simpl; split; assumption.
  - apply H2; simpl; split.
    + assumption.
    + unfold not. intros Hcontra. congruence.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.
Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

Search (negb ?x <> true).
Search ((?x =? ?m) = true -> ?x = ?m).

Example hoare_if1_good: 
  {{ X + Y = Z }}
  if1 ~(Y = 0) then
    X := X + Y
  end
  {{ X = Z }}.
Proof.
  apply hoare_if1; simpl.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold "->>", assn_sub, t_update.
    intros st [H _].
    simpl. assumption.
  - unfold "->>", assn_sub, t_update.
    intros st [H Hy].
    apply eq_true_negb_classical in Hy.
    apply beq_nat_true in Hy.
    lia.
Qed.

End If1.
