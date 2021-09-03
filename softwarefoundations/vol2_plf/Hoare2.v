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



(*
    {{ X = m }} ->>
    {{ X! * 1 = m!                                     }}
      Y := 1;
    {{ X! * Y = m!                                     }}
      while ~(X = 0)
      do   {{ X! * Y = m!  /\  ~(X = 0)                }} ->>
           {{ X! * Y = m!                              }}
         Y := Y × X;
           {{ X! * (Y * X) = m!                        }}
         X := X - 1
           {{ (X - 1)! * (Y * X) = m!                  }}
      end
    {{ X! * Y = m!  /\  X = 0                          }} ->>
    {{ Y = m! }}
*)


(*
  {{ True }} ->>
  {{ min a b  + 0 = min a b                      }}
  X := a;
  {{ min X b  + 0 = min a b                      }}
  Y := b;
  {{ min X Y  + 0 = min a b                      }}
  Z := 0;
  {{ min X Y  + Z = min a b                      }}
  while ~(X = 0) && ~(Y = 0) do
    {{ (min X Y  + Z = min a b) /\ ~(X = 0) /\ ~(Y = 0)    }} ->>
    {{ (min (X - 1) (Y - 1)  + (Z + 1) = min a b)          }}
    X := X - 1;
    {{ (min X (Y - 1)  + (Z + 1) = min a b)                }}
    Y := Y - 1;
    {{ (min X Y  + (Z + 1) = min a b)                      }}
    Z := Z + 1
    {{ (min X Y  + Z = min a b)                        }}
  end
  {{ (min X Y  + Z = min a b) /\ (X = 0) /\ (Y = 0)    }} ->>
  {{ Z = min a b }}
*)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\ forall P', {{P'}} c {{Q}} -> (P' ->> P).

Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
Proof.
  split.
  - eapply hoare_consequence_pre.
    * apply hoare_asgn.
    * verify_assn.
  - intros P' H.
    unfold hoare_triple in H.
    unfold "->>".
    intros st Hp'.
    assert (G: (X !-> st Y + 1; st) X <= 5). {
      simpl in H.
      apply (H st (X !-> st Y + 1; st)).
      + constructor. simpl. reflexivity.
      + assumption.
    }
    unfold t_update in G. simpl in G.
    Search (?c <-> S ?x <= S ?y).
    Search (?x + ?y = ?y + ?x).
    rewrite add_comm in G.
    rewrite <- succ_le_mono in G.
    simpl. 
    apply G.
Qed.

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) <{ X := a }> Q.
Proof.
  split.
  - apply hoare_asgn.
  - intros P' Hc st Hpst.
    unfold assn_sub.
    apply (Hc st).
    + constructor. reflexivity.
    + assumption.
Qed.


Module Himp2.
Import Himp.
Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
  {{ P }} havoc X {{ Q }}  ->  P ->> havoc_pre X Q.
Proof.
  intros P Q X H st Hpst n.
  apply (H st).
  - constructor.
  - assumption.
Qed.
End Himp2.




Inductive dcom : Type :=
| DCSkip (Q : Assertion) (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom) (Q : Assertion)  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)  (* d ->> {{ Q }} *)
.

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.


Declare Scope dcom_scope.
Notation "'skip' {{ P }}" := (DCSkip P)
      (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}" := (DCAsgn l a P)
      (in custom com at level 0, l constr at level 0, a custom com at level 85, P constr, no associativity) : dcom_scope.
Notation "'while' b 'do' {{ P }} d 'end' {{ Q }}" := (DCWhile b P d Q)
      (in custom com at level 89, b custom com at level 99, P constr, Q constr) : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}" := (DCIf b P d P' d' Q)
      (in custom com at level 89, b custom com at level 99, P constr, P' constr, Q constr) : dcom_scope.
Notation "'->>' {{ P }} d" := (DCPre P d)
      (in custom com at level 12, right associativity, P constr) : dcom_scope.
Notation "d '->>' {{ P }}" := (DCPost d P)
      (in custom com at level 10, right associativity, P constr) : dcom_scope.
Notation " d ; d' " := (DCSeq d d')
      (in custom com at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d" := (Decorated P d)
      (in custom com at level 91, P constr) : dcom_scope.
Open Scope dcom_scope.

Example dec0 :=  <{ skip {{ True }} }>.
Example dec1 :=  <{ while true do {{ True }} skip {{ True }} end  {{ True }} }>.


Example dec_while : decorated :=
  <{
    {{ True }}
    while ~(X = 0)
    do
      {{ True /\ ~(X = 0) }}
      X := X - 1
      {{ True }}
    end
    {{ True /\ X = 0}} ->>
    {{ X = 0 }} 
  }>.


Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _            => CSkip
  | DCSeq d1 d2         => CSeq (extract d1) (extract d2)
  | DCAsgn X a _        => CAsgn X a
  | DCIf b _ d1 _ d2 _  => CIf b (extract d1) (extract d2)
  | DCWhile b _ d _     => CWhile b (extract d)
  | DCPre _ d           => extract d
  | DCPost d _          => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Example extract_while_ex :
  extract_dec dec_while = <{while ~(X = 0) do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.


Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P          => P
  | DCSeq _ d2        => post d2
  | DCAsgn _ _ Q      => Q
  | DCIf _ _ _ _ _ Q  => Q
  | DCWhile _ _ _ Q   => Q
  | DCPre _ d         => post d
  | DCPost _ Q        => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.


Example pre_dec_while : pre_dec dec_while = True.
Proof. reflexivity. Qed.

Example post_dec_while : post_dec dec_while = (X = 0)%assertion.
Proof. reflexivity. Qed.


Definition dec_correct (dec : decorated) :=  {{pre_dec dec}} extract_dec dec {{post_dec dec}}.

Example dec_while_triple_correct :
  dec_correct dec_while
 = {{ True }}
   while ~(X = 0) do X := X - 1 end
   {{ X = 0 }}.
Proof. reflexivity. Qed.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q    => (P ->> Q)
  | DCSeq d1 d2 =>
         verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
         ((P /\  b) ->> P1)%assertion
      /\ ((P /\ ~b) ->> P2)%assertion
      /\ (post d1 ->> Q) 
      /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial precondition *)
         (P ->> post d)
      /\ ((post d /\  b) ->> Pbody)%assertion
      /\ ((post d /\ ~b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
         (P ->> P') 
      /\ verification_conditions P' d
  | DCPost d Q =>
         verification_conditions P d 
      /\ (post d ->> Q)
  end.


Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} extract d {{post d}}.
Proof.
  induction d; intros; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence; eauto.
      + eapply hoare_consequence; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1 Hd] ] ].
    eapply hoare_consequence; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
Qed.

Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec -> dec_correct dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

Eval simpl in verification_conditions_dec dec_while.

Example vc_dec_while : verification_conditions_dec dec_while.
Proof. verify_assn. Qed.



Ltac verify :=
  intros;
  apply verification_correct;
  verify_assn.

Theorem Dec_while_correct :  dec_correct dec_while.
Proof. verify. Qed.


Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
  <{
      {{ X = m /\ Z = p }} ->>
      {{ Z - X = p - m }}
    while ~(X = 0)
    do {{ Z - X = p - m /\ X <> 0 }} ->>
         {{ (Z - 1) - (X - 1) = p - m }}
       Z := Z - 1
         {{ Z - (X - 1) = p - m }} ;
       X := X - 1
         {{ Z - X = p - m }}
    end
      {{ Z - X = p - m /\ X = 0 }} ->>
      {{ Z = p - m }} 
  }>.
Theorem subtract_slowly_dec_correct : forall m p,
  dec_correct (subtract_slowly_dec m p).
Proof. verify. (* this grinds for a bit! *) Qed.




(* Definition swap : com := *)
(*   <{ X := X + Y; *)
(*      Y := X - Y; *)
(*      X := X - Y }>. *)
Definition swap_dec (m n:nat) : decorated :=
  <{
       {{ X = m /\ Y = n}} ->>
       {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
      X := X + Y
       {{ X - (X - Y) = n /\ X - Y = m }};
      Y := X - Y
       {{ X - Y = n /\ Y = m }};
      X := X - Y
       {{ X = n /\ Y = m}} 
  }>.
Theorem swap_correct : forall m n,  dec_correct (swap_dec m n).
Proof. verify. Qed.


Definition div_mod_dec (a b : nat) : decorated :=
  <{
      {{ True }} ->>
      {{ b * 0 + a = a }}
      X := a
      {{ b * 0 + X = a }};
      Y := 0
      {{ b * Y + X = a }};
      while b <= X do
        {{ b * Y + X = a /\ b <= X }} ->>
        {{ b * (Y + 1) + (X - b) = a }}
        X := X - b
        {{ b * (Y + 1) + X = a }};
        Y := Y + 1
        {{ b * Y + X = a }}
      end
      {{ b * Y + X = a /\ ~(b <= X) }} ->>
      {{ b * Y + X = a /\ (X < b) }} 
  }>.
Theorem div_mod_dec_correct : forall a b,  dec_correct (div_mod_dec a b).
Proof.
  verify.
Qed.



Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Definition find_parity_dec' (m:nat) : decorated :=
  <{
        {{ X = m }} ->>
        {{ ap ev X <-> ev m }}
       while 2 <= X do
          {{ (ap ev X <-> ev m) /\ 2 <= X }} ->>
          {{ ap ev (X - 2) <-> ev m }}
          X := X - 2
          {{ ap ev X <-> ev m }}
       end
       {{ (ap ev X <-> ev m) /\ ~(2 <= X) }} ->>
       {{ X=0 <-> ev m }} 
  }>.

Lemma l4 : forall m,
  2 <= m -> (ev (m - 2) <-> ev m).
Proof.
  induction m; intros. split; intro; constructor.
  destruct m. inversion H. inversion H1. simpl in *.
  rewrite <- minus_n_O in *. split; intro.
    constructor. assumption.
    inversion H0. assumption.
Qed.

Theorem find_parity_correct' : forall m,  dec_correct (find_parity_dec' m).
Proof.
  verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (2 <=? (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; intuition; eauto; try lia.
  - (* invariant preserved (part 1) *)
    rewrite l4 in H0; eauto.
  - (* invariant preserved (part 2) *)
    rewrite l4; eauto.
  - (* invariant strong enough to imply conclusion
       (-> direction) *)
    apply H0. constructor.
  - (* invariant strong enough to imply conclusion
       (<- direction) *)
      destruct (st X) as [| [| n] ]. (* by H1 X can only be 0 or 1 *)
      + (* st X = 0 *)
        reflexivity.
      + (* st X = 1 *)
        inversion H.
      + (* st X = 2 *)
        lia.
Qed.



Example slow_assignment_dec (m : nat) : decorated :=
  <{  {{ X = m }} ->>
      {{ X + 0 = m }}
      Y := 0
      {{ X + Y = m }};
      while ~(X = 0) do
        {{ X + Y = m /\ ~(X = 0) }} ->>
        {{ (X - 1) + (Y + 1) = m }}
        X := X - 1
        {{ X + (Y + 1) = m }};
        Y := Y + 1
        {{ X + Y = m }}
      end
      {{ X + Y = m /\ (X = 0) }} ->>
      {{ Y = m }}
  }>.

Theorem slow_assignment_dec_correct : forall m,  dec_correct (slow_assignment_dec m).
Proof. verify. Qed.


Definition foo1: nat -> nat -> nat := fun a b => a + b.
Definition foo2: nat -> nat -> Prop := fun a b => a = b.

Definition foo3: foo2 1 1. (* Theorem / Lemma is just functions *)
Proof. reflexivity. Qed.



Fixpoint fib n :=
  match n with
  | 0    => 1
  | S n' => match n' with
            | 0     => 1
            | S n'' => fib n' + fib n''
            end
  end.

Lemma fib_eqn : forall n,
  n > 0 -> fib n + fib (pred n) = fib (1 + n).
Proof.
  intros n Hgt0.
  destruct n as [| n'].
  - inversion Hgt0.
  - simpl. reflexivity.
Qed.

Definition T : string := "T".

Open Scope com_scope.
Definition fib_prog (n: nat) : com := 
  <{
    X := 1;
    Y := 1;
    Z := 1;
    while ~(X = 1 + n) do
      T := Z;
      Z := Z + Y;
      Y := T;
      X := 1 + X
    end
  }>.


Open Scope dcom_scope.
Definition dfib (n: nat) : decorated := 
  <{
    {{ True }} ->>
    {{ 1 = 1 /\ 1 = 1 /\ 1 = 1 }}
    X := 1
    {{ X = 1 /\ 1 = 1 /\ 1 = 1 }};
    Y := 1
    {{ X = 1 /\ Y = 1 /\ 1 = 1 }};
    Z := 1
    {{ X = 1 /\ Y = 1 /\ Z = 1 }} ->>
    {{ X > 0 /\ Y = (ap fib (X - 1)) /\ Z = (ap fib X) }};
    while ~(X = 1 + n) do
      {{ X > 0 /\ Y = (ap fib (X - 1)) /\ Z = (ap fib X) /\ ~(X = 1 + n) }}
      T := Z
      {{ X > 0 /\ Y = (ap fib (X - 1)) /\ Z = (ap fib X) /\ T = (ap fib X) /\ ~(X = 1 + n) }};
      Z := Z + Y 
      {{ X > 0 /\ Y = (ap fib (X - 1)) /\ Z = (ap fib (1 + X)) /\ T = (ap fib X) /\ ~(X = 1 + n) }};
      Y := T
      {{ X > 0 /\ Y = (ap fib X) /\ Z = (ap fib (1 + X)) /\ T = (ap fib X) /\ ~(X = 1 + n)  }} ->>
      {{ X > 0 /\ Y = (ap fib ((X + 1) - 1)) /\ Z = (ap fib (1 + X)) }};
      X := 1 + X
      {{ X > 0 /\ Y = (ap fib (X - 1)) /\ Z = (ap fib X) }}
    end
    {{ X > 0 /\ Y = (ap fib (X - 1)) /\ Z = (ap fib X) /\ (X = 1 + n) }} ->>
    {{ Y = fib n }}
  }>.

Lemma sn_1: forall n, S n - 1 = n.
Proof. intros n. simpl. lia. Qed.

Lemma n_1_1: forall n, n + 1 - 1 = n.
Proof. intros n. lia. Qed.

Lemma n_0: forall n, n - 0 = n.
Proof. intros n. lia. Qed.

Theorem dfib_correct : forall n,  dec_correct (dfib n).
Proof. verify.
  - destruct (st X). inversion H.
    rewrite -> sn_1. reflexivity.
  - rewrite -> n_1_1. reflexivity.
  - rewrite -> n_1_1.
    rewrite -> n_0. reflexivity.
  - rewrite -> sn_1. reflexivity.
Qed.

(*
  Exercise: 5 stars, advanced, optional (improve_dcom)
  The formal decorated programs defined in this section are intended to 
  look as similar as possible to the informal ones defined earlier in the 
  chapter. If we drop this requirement, we can eliminate almost all annotations,
   just requiring final postconditions and loop invariants to be provided explicitly. 
  Do this -- i.e., define a new version of dcom with as few annotations as possible 
  and adapt the rest of the formal development leading up to the verification_correct theorem. 
*)

Module LastEx.
End LastEx.

