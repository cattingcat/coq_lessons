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




Inductive sinstr : Type :=
  | SPush (n : nat)
  | SLoad (x : string)
  | SPlus
  | SMinus
  | SMult.

Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr) : list nat :=
  match prog with
  | SPush n :: t => s_execute st (n :: stack) t
  | SLoad a :: t => s_execute st ((st a) :: stack) t
  | SPlus   :: t => 
    match stack with
    | x :: y :: r => s_execute st ((y + x) :: r) t
    | r => s_execute st r t
    end
  | SMinus   :: t => 
    match stack with
    | x :: y :: r => s_execute st ((y - x) :: r) t
    | r => s_execute st r t
    end
  | SMult   :: t => 
    match stack with
    | x :: y :: r => s_execute st ((y * x) :: r) t
    | r => s_execute st r t
    end
  | _ => stack
end.

Check s_execute.

Example s_execute1 : s_execute empty_st [] [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. unfold s_execute. reflexivity. Qed.

Example s_execute2 : s_execute (X !-> 3) [3;4] [SPush 4; SLoad X; SMult; SPlus] = [15; 4].
Proof. simpl. reflexivity. Qed.


Fixpoint s_compile (e : aexp) : list sinstr := 
  match e with
  | ANum n => SPush n :: nil
  | AId  x => SLoad x :: nil
  | AMult  a1 a2 => (s_compile a1 ++ s_compile a2) ++ [SMult]
  | APlus  a1 a2 => (s_compile a1 ++ s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1 ++ s_compile a2) ++ [SMinus]
  end.

Example s_compile1 : s_compile <{ X - (2 * Y) }> = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. simpl. reflexivity. Qed.

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  intros st p1.
  induction p1 as [| h1 t1 IH ].
  - simpl. intros. reflexivity.
  - intros.
    destruct h1.
    + simpl. rewrite IH. reflexivity.
    + simpl. rewrite IH. reflexivity.
    + simpl. 
      destruct stack as [| x1 [| x2 xt] ].
      * apply IH.
      * apply IH.
      * apply IH.
    + simpl. 
      destruct stack as [| x1 [| x2 xt] ].
      * apply IH.
      * apply IH.
      * apply IH.
    + simpl. 
      destruct stack as [| x1 [| x2 xt] ].
      * apply IH.
      * apply IH.
      * apply IH.
Qed.

Search (?a + ?b = ?b + ?a).

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  intros st e.
  induction e;
    try (simpl; reflexivity);
    try (
      intros; simpl;
      rewrite app_assoc_reverse;
      rewrite execute_app;
      rewrite execute_app;
      rewrite IHe1;
      simpl;
      rewrite IHe2;
      reflexivity).
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof. intros. apply s_compile_correct_aux. Qed.


Fixpoint beval' (st: state) (b : bexp) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BEq a1 a2  => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2  => (aeval st a1) <=? (aeval st a2)
  | BNot b1    => negb (beval' st b1)
  | <{b1 && b2}> => if beval' st b1 then beval' st b2 else false
  end.

Theorem shor_beval_correct: forall st b, beval' st b = beval st b.
Proof.
  intros.
  induction b;
    try (reflexivity).
Qed.

End AExp.




Module BreakImp.
Import AExp.

Inductive com : Type :=
  | CSkip
  | CBreak (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'" :=  CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=  (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=   (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.


Definition tst : com := <{
       X := 0;
       Y := 1;
       while ~(0 = Y) do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end
}>.

Inductive result : Type :=
  | SContinue
  | SBreak.
Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st) / SContinue
  | E_SeqCont : forall c1 c2 st st' st'' r,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / r ->
      st =[ c1 ; c2 ]=> st'' / r
  | E_SeqBr : forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1 ; c2 ]=> st' / SBreak
  | E_IfTrue : forall st st' b c1 c2 r,
      beval st b = true ->
      st =[ c1 ]=> st' / r ->
      st =[ if b then c1 else c2 end]=> st' / r
  | E_IfFalse : forall st st' b c1 c2 r,
      beval st b = false ->
      st =[ c2 ]=> st' / r->
      st =[ if b then c1 else c2 end]=> st' / r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st / SContinue
  | E_WhileTrueCont : forall st st' st'' b c r,
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / r ->
      st =[ while b do c end ]=> st'' / r
  | E_WhileTrueBr : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ while b do c end ]=> st' / SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').


Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof. intros. 
  inversion H. inversion H2. inversion H5. subst. inversion H5. apply H3. Qed.

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof. intros. 
  remember (<{ while b do c end }>) as K eqn:Ek.
  induction H;
    try (discriminate Ek).
  - reflexivity.
  - apply IHceval2. apply Ek.
  - reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros.
  apply E_WhileTrueBr.
  apply H.
  apply H0.
Qed.

Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  intros. apply (E_SeqCont c1 c2 st st' st''). apply H. apply H0. Qed. 

Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  intros. apply (E_SeqBr c1 c2 st st'). apply H. Qed. 


Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
  remember (<{ while b do c end }>) as K eqn:Ek.
  induction H;
    try (discriminate Ek).
  - injection Ek as Ek1 Ek2. rewrite Ek1 in H. rewrite H in H0. discriminate H0.
  - apply IHceval2. apply Ek. apply H0.
  - exists st. injection Ek as Ek1 Ek2. rewrite Ek2 in H1. apply H1.
Qed.


Lemma elim_second_skip: forall c st st' s, st =[ c; skip ]=> st' / s -> st =[ c ]=> st' / s.
Proof.
  intros. 
  remember (<{ c; skip }>) as k eqn:Ek.
  induction H; 
    try (discriminate Ek).
  - injection Ek as Ek1 Ek2.
    rewrite Ek2 in H0.
    inversion H0.
    rewrite <- H4.
    rewrite -> Ek1 in H.
    apply H.
  - injection Ek as Ek1 Ek2.
    rewrite <- Ek1.
    apply H.
Qed.


Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros.
  generalize dependent st2.
  generalize dependent s2.
  induction H; intros.
  - inversion H0. split. reflexivity. reflexivity.
  - inversion H0. split. reflexivity. reflexivity.
  - inversion H0. split. subst. reflexivity. reflexivity.
  - apply IHceval2.
    inversion H1.
    + destruct (IHceval1 _ _ H4). rewrite <- H9 in H8. apply H8.
    + destruct (IHceval1 _ _ H7). discriminate H9.
  - apply IHceval.
    inversion H0.
    + destruct (IHceval _ _ H3). discriminate H9.
    + apply H6.
  - apply IHceval.
    inversion H1.
    + apply H9.
    + rewrite H8 in H. discriminate H.
  - apply IHceval.
    inversion H1.
    + rewrite H8 in H. discriminate H.
    + apply H9.
  - inversion H0.
    + split. reflexivity. reflexivity.
    + rewrite H3 in H. discriminate H.
    + rewrite H3 in H. discriminate H.
  - apply IHceval2.
    inversion H2.
    + rewrite <- H7 in H8. rewrite H8 in H. discriminate H.
    + destruct (IHceval1 _ _ H6). rewrite <- H11 in H10. apply H10.
    + destruct (IHceval1 _ _ H9). discriminate H11.
  - inversion H1.
    + rewrite <- H6 in H7. rewrite H7 in H. discriminate H.
    + destruct (IHceval _ _ H5). discriminate H11.
    + destruct (IHceval _ _ H8). rewrite H9. split. reflexivity. reflexivity.
Qed.


End BreakImp.



(* TODO *)
(*
Exercise: 4 stars, standard, optional (add_for_loop)
Add C-style for loops to the language of commands, update the ceval definition 
to define the semantics of for loops, and add cases for for loops as needed so that 
all the proofs in this file are accepted by Coq.
A for loop should be parameterized by (a) a statement executed initially, (b) a test 
that is run on each iteration of the loop to determine whether the loop should continue, 
(c) a statement executed at the end of each loop iteration, and (d) a statement that makes 
up the body of the loop. (You don't need to worry about making up a concrete Notation for for
 loops, but feel free to play with this too if you like.) *)



End Imp2.
