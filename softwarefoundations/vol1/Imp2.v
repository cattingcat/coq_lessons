Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps. Import Maps.

(* Example:

       Z := X;
       Y := 1;
       while ~(Z = 0) do
         Y := Y × Z;
         Z := Z - 1
       end
*)

Module Imp2.

Module AExp.

Definition state := total_map nat. (* new *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* new *)
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



Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e           (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x             (in custom com, x at level 99) : com_scope.
Notation "x" := x                 (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y)   (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y)  (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y)   (in custom com at level 40, left associativity).
Notation "'true'" := true         (              at level 1).
Notation "'true'" := BTrue        (in custom com at level 0).
Notation "'false'" := false       (              at level 1).
Notation "'false'" := BFalse      (in custom com at level 0).
Notation "x <= y" := (BLe x y)    (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y)     (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y)   (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b)      (in custom com at level 75, right associativity).



Open Scope com_scope.


Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Print example_bexp.

Set Printing Coercions.
Print example_bexp.
Unset Printing Coercions.



(* Evaluation *)

Fixpoint aeval (st: state) (a : aexp) : nat :=
  match a with
  | ANum n       => n
  | AId x        => st x 
  | APlus a1 a2  => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2  => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st: state) (b : bexp) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BEq a1 a2  => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2  => (aeval st a1) <=? (aeval st a2)
  | BNot b1    => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2) (* patterns notation *)
  end.



Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example aexp1 : aeval (X !-> 5) <{ 3 + (X * 2) }> = 13.
Proof. reflexivity. Qed.

Example aexp2 : aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }> = 20.
Proof. reflexivity. Qed.

Example bexp1 : beval (X !-> 5) <{ true && ~(X <= 4) }> = true.
Proof. reflexivity. Qed.



(* c := skip | x := a | c ; c | if b then c else c end | while b do c end *)
Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'" := CSkip (in custom com at level 0) : com_scope.
Notation "x := y" := (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" := (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.


Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.
Print fact_in_coq.

Unset Printing Notations.
Print fact_in_coq.
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
Unset Printing Coercions.


Locate "&&".
Locate ";".
Locate "while".
Locate aexp.



Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st (* bogus *)
  end.



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


Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  where "st =[ c ]=> st'" := (ceval c st st').




Definition example1Prog : com := <{
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  }>.

Example ceval_example1:
  empty_st =[ example1Prog ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Asgn. reflexivity.
Qed.


Definition example2Prog : com := <{
    X := 0;
    Y := 1;
    Z := 2
  }>.

Example ceval_example2:
  empty_st =[ example2Prog ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply (E_Seq _ _ empty_st (X !-> 0) _).
  - apply E_Asgn. simpl. reflexivity.
  - apply (E_Seq _ _ _ (Y !-> 1; X !-> 0) _).
    + apply E_Asgn. simpl. reflexivity.
    + apply E_Asgn. simpl. reflexivity.
Qed.

Definition pup_to_n : com := <{
    Y := 0;
    while ~(X <= 0) do
       Y := Y + X;
       X := X - 1
     end
  }>.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  apply (E_Seq _ _ _ (Y !-> 0; X !-> 2) _).
  - apply E_Asgn. simpl. reflexivity.
  - apply (E_WhileTrue 
                        (Y !-> 0 ; X !-> 2) 
                        (X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2) 
                         _).
    -- simpl. reflexivity.
    -- apply (E_Seq _ _ _ (Y !-> 2; Y!-> 0; X !-> 2) (X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2)).
       + assert (G: aeval (Y !-> 0; X !-> 2) <{ Y + X}> = 2). { simpl. unfold t_update. simpl. reflexivity. }
         apply (E_Asgn _ _ 2 Y G).
       + assert (G: aeval (Y!-> 2; Y !-> 0; X !-> 2) <{ X - 1 }> = 1). { simpl. reflexivity. }
         apply (E_Asgn _ _ 1 X G).
    -- apply (E_WhileTrue 
                        (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2) 
                        (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2)
                         _).
       --- simpl. reflexivity.
       --- apply (E_Seq _ _ _ (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2) (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2)).
           + assert (G: aeval (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2) <{ Y + X }> = 3). { simpl. unfold t_update. simpl. reflexivity. }
             apply (E_Asgn _ _ 3 Y G).
           + assert (G: aeval (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2) <{ X - 1 }> = 0). { simpl. reflexivity. }
             apply (E_Asgn _ _ 0 X G).
       --- apply (E_WhileFalse).
           simpl. reflexivity.
Qed.


Definition plus2 : com :=
  <{ X := X + 2 }>.
Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.
Theorem XtimesYinZ_spec : forall st n m st',
  st X = n ->
  st Y = m ->
  st =[ XtimesYinZ ]=> st' ->
  st' Z = n * m.
Proof.
  intros st n m st' HX HY Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.


Definition loop : com :=
  <{ while true do skip end }>.
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.
  induction contra.
  - discriminate Heqloopdef.
  - discriminate Heqloopdef.
  - discriminate Heqloopdef.
  - discriminate Heqloopdef.
  - discriminate Heqloopdef.
  - injection Heqloopdef as H1 H2.
    rewrite H1 in H. simpl in H.
    discriminate H.
  - injection Heqloopdef as H1 H2.
    apply IHcontra2.
    rewrite H1, H2.
    reflexivity.
Qed.




Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }>                      => true
  | <{ _ := _ }>                    => true
  | <{ c1 ; c2 }>                   => andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }>  => andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>          => false
  end.


(*  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
*)

Inductive no_whilesR: com -> Prop :=
  | NW_Skip : no_whilesR CSkip
  | NW_Asgn (x: string) (a: aexp) : no_whilesR (CAsgn x a)
  | NW_Seq (c1 c2 : com) (H1: no_whilesR c1) (H2: no_whilesR c2) : no_whilesR (CSeq c1 c2)
  | NW_If (b : bexp) (c1 c2 : com) (H1: no_whilesR c1) (H2: no_whilesR c2) : no_whilesR (CIf b c1 c2)
.

Search (?a && ?b = true -> ?a = true /\ ?b = true).
  

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intro. split.
  - intro H.
    induction c.
    + apply NW_Skip.
    + apply NW_Asgn.
    + simpl in H.
      apply andb_prop in H.
      destruct H as [Hl Hr].
      apply NW_Seq.
      apply IHc1. apply Hl.
      apply IHc2. apply Hr.
    + simpl in H.
      apply andb_prop in H.
      destruct H as [Hl Hr].
      apply NW_If.
      apply IHc1. apply Hl.
      apply IHc2. apply Hr.
    + simpl in H. discriminate H.
  - intro H.
    induction H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHno_whilesR1. rewrite IHno_whilesR2. reflexivity.
    + simpl. rewrite IHno_whilesR1. rewrite IHno_whilesR2. reflexivity.
Qed.


Theorem no_whiles_terminates : forall p st, 
  no_whilesR p -> exists st', st =[ p ]=> st'.
Proof.
  intros.
  generalize dependent st.
  induction H.
  - intros. exists st. apply (E_Skip st).
  - intros. exists (x !-> (aeval st a) ; st). apply (E_Asgn st a _ ). reflexivity.
  - intros. 
    destruct (IHno_whilesR1 st) as [st' H1].
    destruct (IHno_whilesR2 st') as [st'' H2].
    exists st''.
    apply (E_Seq c1 c2 st st' st'' H1 H2).
  - intros.
    destruct (beval st b) eqn:E.
    + destruct (IHno_whilesR1 st) as [st' H1].
      exists st'. 
      apply (E_IfTrue st st' b c1 c2 E H1).
    + destruct (IHno_whilesR2 st) as [st' H1].
      exists st'. 
      apply (E_IfFalse st st' b c1 c2 E H1).
Qed.


End AExp.























End Imp2.
