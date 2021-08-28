Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.


(*    {{ True }}
      if X ≤ Y then
          {{ True /\ X ≤ Y           }} ->>
          {{ Y = X + Y - X           }}
        Z := Y - X
          {{ Y = X + Z               }}
      else
          {{ True /\ ~(X ≤ Y)        }} ->>
          {{ X + Z = X + Z           }}
        Y := X + Z
          {{ Y = X + Z               }}
      end
        {{ Y = X + Z }}
*)



(*
        (1)      {{ True }}
               while ~(X = 0) do
        (2)        {{ True ∧ X ≠ 0 }} ->>
        (3)        {{ True }}
                 X := X - 1
        (4)        {{ True }}
               end
        (5)      {{ True ∧ ~(X ≠ 0) }} ->>
        (6)      {{ X = 0 }}
*)
Definition reduce_to_zero' : com :=
  <{ while ~(X = 0) do X := X - 1 end }>.
Theorem reduce_to_zero_correct' :
  {{True}} reduce_to_zero' {{X = 0}}.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    + (* Loop body preserves invariant *)
      (* Need to massage precondition before hoare_asgn applies *)
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* Proving trivial implication (2) ->> (3) *)
        unfold assn_sub, "->>". simpl. intros. exact I.
  - (* Invariant and negated guard imply postcondition *)
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse.
Qed.


Ltac verify_assn :=
  repeat split;
  simpl; unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq; [| (intro X; inversion X; fail)] ) );
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try lia.

Theorem reduce_to_zero_correct''' :
  {{True}} reduce_to_zero' {{X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * verify_assn.
  - verify_assn.
Qed.


(*
       X := m;
       Y := 0;
       while n ≤ X do
         X := X - n;
         Y := Y + 1
       end;
  
    Y = m / n
    X = m % n

    n × Y + X = m ∧ X < n. 

      (1)    {{ True }} ->>
      (2)    {{ n × 0 + m = m }}
           X := m;
      (3)    {{ n × 0 + X = m }}
           Y := 0;
      (4)    {{ n × Y + X = m }}
           while n ≤ X do
      (5)      {{ n × Y + X = m ∧ n ≤ X }} ->>
      (6)      {{ n × (Y + 1) + (X - n) = m }}
             X := X - n;
      (7)      {{ n × (Y + 1) + X = m }}
             Y := Y + 1
      (8)      {{ n × Y + X = m }}
           end
      (9)    {{ n × Y + X = m ∧ ¬(n ≤ X) }} ->>
     (10)    {{ n × Y + X = m ∧ X < n }}
*)


(*
      {{ X = m }}
      {{ X = m /\ 0 = 0}}
      Y := 0;
      {{ X = m /\ Y = 0}}
      {{ X + Y = m /\ ~(X = 0) }}
      while ~(X = 0) do
        {{ X - 1 + Y + 1 = m /\ ~(X = 0) }}
        X := X - 1;
        {{ X + Y + 1 = m /\ ~(X = 0) }}
        Y := Y + 1
        {{ X + Y = m /\ ~(X = 0) }}
      end
      {{ X + Y = m /\ X = 0 }}
      {{ Y = m }}
*)
Definition  slow_assignment_prog : com :=
  <{ 
      Y := 0;
      while ~(X = 0) do
        X := X - 1;
        Y := Y + 1
      end
  }>.

Definition body_slow_assignment_prog: com :=
  <{
    X := X - 1;
    Y := Y + 1
  }>.
Lemma tst: forall (m: nat), {{ X + Y = m /\ ~(X = 0)}} body_slow_assignment_prog {{ X + Y = m }}.
Proof. intro m. unfold body_slow_assignment_prog.
  eapply hoare_seq.
  - (* Y *)
    apply hoare_asgn.
  - (* X *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + (* func *)
      verify_assn.
Qed.


Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x, 2 <= x -> parity (x - 2) = parity x.
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + lia.
    + inversion H; subst; simpl.
      * reflexivity.
      * rewrite sub_0_r. reflexivity.
Qed.

Lemma parity_lt_2 : forall x, ~(2 <= x) -> parity x = x.
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + reflexivity.
    + lia.
Qed.

Theorem parity_correct : forall (m:nat),
  {{ X = m }}
  while 2 <= X do
    X := X - 2
  end
  {{ X = parity m }}.
Proof.
  intro m.
  apply hoare_consequence_pre with (P' := assert (ap parity X = parity m)).
  --  eapply hoare_consequence_post.
      - eapply hoare_while.
        + (* While body *)
          eapply hoare_consequence_pre.
          * apply hoare_asgn.
          * verify_assn.
            rewrite <- H.
            apply (parity_ge_2 (st X)).
            destruct (st X). discriminate H0.
            destruct n. discriminate H0.
            lia.
      - verify_assn.
        rewrite <- H. symmetry.
        apply parity_lt_2.
        destruct (st X). lia.
        destruct n. lia.
        lia.
  -- verify_assn.
Qed.
