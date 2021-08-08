Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.

(* Example:

       Z := X;
       Y := 1;
       while ~(Z = 0) do
         Y := Y × Z;
         Z := Z - 1
       end
*)

Module Imp.

Module AExp.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


(* Evaluation *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n       => n
  | APlus a1 a2  => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2  => (aeval a1) * (aeval a2)
  end.

Example test_aeval1: aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BEq a1 a2  => (aeval a1) =? (aeval a2)
  | BLe a1 a2  => (aeval a1) <=? (aeval a2)
  | BNot b1    => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.


(* Optimization *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n            => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2       => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2      => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2       => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.


(* Tacticals *)
Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.


Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n; simpl; reflexivity. (* ; allows to apply tactics to both branches *)
Qed.


Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* try - tries to apply tactics, and leave term as is if it is not possible *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity. Qed.

(*
  T;T' - apply T' to all branches
  T;[T1|...|Tn] - apply T1 to first, T2 to second, etc.
*)


(* repeat - repeats tactic until it stop doing progress *)
Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.


Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with 
  | BEq a1 a2  => BEq  (optimize_0plus a1)   (optimize_0plus a2)
  | BLe a1 a2  => BLe  (optimize_0plus a1)   (optimize_0plus a2)
  | BNot b     => BNot (optimize_0plus_b b)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  | o => o
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof. intro b.
  induction b; 
    try (reflexivity);
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try (simpl; rewrite IHb1; rewrite IHb2; reflexivity);
    try (simpl; rewrite optimize_0plus_sound'; rewrite optimize_0plus_sound'; reflexivity).
  - simpl. rewrite IHb. reflexivity.
Qed.


(* Custom tactics (see also docs/books about Ltac) *)
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.



(* lia - uses https://en.wikipedia.org/wiki/Presburger_arithmetic to solve math expression *)
Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof. intros. lia. Qed.

Example add_comm__lia : forall m n,
    m + n = n + m.
Proof. intros. lia. Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof. intros. lia. Qed.


(*

    clear H: Delete hypothesis H from the context.
    subst x: For a variable x, find an assumption x = e or e = x in the context, 
      replace x with e throughout the context and current goal, and clear the assumption.
    subst: Substitute away all assumptions of the form x = e or e = x (where x is a variable).
    rename... into...: Change the name of a hypothesis in the proof context. 
      For example, if the context includes a variable named x, then rename x into y will 
      change all occurrences of x to y.
    assumption: Try to find a hypothesis H in the context that exactly matches the goal; 
      if one is found, solve the goal.
    contradiction: Try to find a hypothesis H in the current context that is 
      logically equivalent to False. If one is found, solve the goal.
    constructor: Try to find a constructor c (from some Inductive definition in the current environment) 
      that can be applied to solve the current goal. If one is found, behave like apply c.

*)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) : 
    (ANum n) ==> n
  | E_APlus  (e1 e2 : aexp) (n1 n2 : nat) (H1: e1 ==> n1) (H2: e2 ==> n2) : 
    (APlus  e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) (H1: e1 ==> n1) (H2: e2 ==> n2) : 
    (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult  (e1 e2 : aexp) (n1 n2 : nat) (H1: e1 ==> n1) (H2: e2 ==> n2) : 
    (AMult  e1 e2) ==> (n1 * n2)
  where "e '==>' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue  : 
    BTrue  ==>b true
  | E_BFalse : 
    BFalse ==>b false
  | E_BEq (e1 e2: aexp) (n1 n2 : nat) (H1: e1 ==> n1) (H2: e2 ==> n2) : 
    BEq e1 e2 ==>b (n1 =? n2)
  | E_BLe (e1 e2: aexp) (n1 n2 : nat) (H1: e1 ==> n1) (H2: e2 ==> n2) : 
    BLe e1 e2 ==>b (n1 <=? n2)
  | E_BNot (e1: bexp) (b1: bool) (H1: e1 ==>b b1): 
    BNot e1 ==>b (negb b1)
  | E_BAnd (e1 e2: bexp) (b1 b2: bool) (H1: e1 ==>b b1) (H2: e2 ==>b b2): 
    BAnd e1 e2 ==>b (andb b1 b2)
  where "e '==>b' b" := (bevalR e b) : type_scope.

Lemma refl_eval: forall e, e ==> aeval e.
Proof.
  intro e.
  induction e.
  - simpl. constructor.
  - simpl. constructor. apply IHe1. apply IHe2.
  - simpl. constructor. apply IHe1. apply IHe2.
  - simpl. constructor. apply IHe1. apply IHe2.
Qed.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  intros.
  split.
  - intro H.
    induction H; simpl;
      try (reflexivity);
      try (apply aeval_iff_aevalR' in H1; apply aeval_iff_aevalR' in H2;
           rewrite H1; rewrite H2; reflexivity).
    + rewrite IHbevalR. reflexivity.
    + rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.
  - intro H.
    generalize dependent bv.
    induction b;
      try (intros; simpl in H; rewrite <- H; constructor; reflexivity).
    + intros. simpl in H. rewrite <- H. constructor.
      * apply refl_eval.
      * apply refl_eval.
    + intros. simpl in H. rewrite <- H. constructor.
      * apply refl_eval.
      * apply refl_eval.
    + intros. simpl in H. rewrite <- H. constructor. apply IHb. reflexivity.
    + intros. simpl in H. rewrite <- H. constructor.
      * apply IHb1. reflexivity.
      * apply IHb2. reflexivity.
Qed.

End AExp.























End Imp.
