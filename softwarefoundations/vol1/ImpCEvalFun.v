From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import Imp2 Maps.

Module ImpCEvalFun.
Import Imp2.AExp.
Import Maps.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ l := a1 }> =>
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> =>
        st (* bogus *)
  end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O     => empty_st
  | S i'  =>
    match c with
      | <{ skip }>    => st
      | <{ l := a1 }> => (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          let st' := ceval_step2 st c1 i' in ceval_step2 st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in ceval_step2 st' c i'
          else st
    end
  end.


Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O    => None
  | S i' =>
    match c with
      | <{ skip }>    => Some st
      | <{ l := a1 }> => Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None     => None
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None     => None
               end
          else Some st
    end
  end.




Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None   => None
       end)
   (right associativity, x pattern, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O    => None
  | S i' =>
    match c with
      | <{ skip }>    => Some st
      | <{ l := a1 }> => Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.



Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st
     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>
     = Some (2, 0, 4).
Proof. reflexivity. Qed.

Definition pup_to_n : com := <{
  Y := 0;
  while ~(X = 0) do
    Y := Y + X;
    X := X - 1
  end
}>.

Example pup_to_n_1 : test_ceval (X !-> 5) pup_to_n = Some (0, 15, 0).
Proof. unfold test_ceval. simpl. reflexivity. Qed.

Definition check_even : com := <{
  while 2 <= X do
    X := X - 2
  end;

  if X = 0 then Z := 0 else skip end;
  if X = 1 then Z := 1 else skip end
}>.

Example check_even_5 : test_ceval (X !-> 5) check_even = Some (1, 0, 1).
Proof. unfold test_ceval. simpl. reflexivity. Qed.

Example check_even_4 : test_ceval (X !-> 4) check_even = Some (0, 0, 0).
Proof. unfold test_ceval. simpl. reflexivity. Qed.









Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.
  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* skip *) apply E_Skip.
      + (* := *) apply E_Asgn. reflexivity.
      + (* ; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.
      + (* if *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
      + (* while *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.


Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + (* skip *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.
    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval. Qed.

Theorem ceval__ceval_step: forall c st st',
  st =[ c ]=> st' -> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  - (* skip *)
    exists 1. simpl. reflexivity.
  - (* := *)
    exists 1. simpl. rewrite H. reflexivity.
  - (* ; *)
    destruct IHHce1 as [i1 IH1].
    destruct IHHce2 as [i2 IH2].
    exists (S i1 + S i2).
    simpl.
    assert (G1: i1 <= i1 + S i2) by lia.
    rewrite -> (ceval_step_more i1 (i1 + S i2) st  st'  c1 G1 IH1).
    assert (G2: i2 <= i1 + S i2) by lia.
    rewrite -> (ceval_step_more i2 (i1 + S i2) st' st'' c2 G2 IH2).
    reflexivity.
  - (* if true *)
    destruct IHHce as [i IH].
    exists (S i).
    simpl. rewrite -> H.
    assumption.
  - (* if false *)
    destruct IHHce as [i IH].
    exists (S i).
    simpl. rewrite -> H.
    assumption.
  - (* while false *)
    exists 1.
    simpl. rewrite -> H.
    reflexivity.
  - (* while true *)
    destruct IHHce1 as [i1 IH1].
    destruct IHHce2 as [i2 IH2].
    exists (S i1 + S i2).
    simpl. rewrite -> H.
    assert (G1: i1 <= i1 + S i2) by lia.
    rewrite -> (ceval_step_more i1 (i1 + S i2) st  st'  c G1 IH1).
    assert (G2: i2 <= i1 + S i2) by lia.
    rewrite -> (ceval_step_more i2 (i1 + S i2) st' st'' _ G2 IH2).
    reflexivity.
Qed.


Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st' <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.



Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia. Qed.

End ImpCEvalFun.