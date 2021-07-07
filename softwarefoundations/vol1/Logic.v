Module Logic.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.


Check (3 = 3) : Prop.
Check (forall n m : nat, n + m = m + n) : Prop.
Check (2 = 2) : Prop.
Check (3 = 2) : Prop.
Check (forall n : nat, n = 2) : Prop.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true : plus_claim.
Proof. reflexivity. Qed.


Definition is_three (n : nat) : Prop := n = 3.
Check is_three : nat -> Prop.


Definition injective {A B} (f : A -> B) := forall x y : A, (f x = f y) -> (x = y).
Lemma succ_inj : injective S.
Proof.
  intros n m H. 
  assert (G : forall n, pred (S n) = n). {
    reflexivity.
  }
  rewrite <- (G n).
  rewrite -> H.
  simpl.
  reflexivity.
(*
  injection H as H1. 
  apply H1.
*)
Qed.

(* eq is (=) *)
Check @eq : forall A : Type, A -> A -> Prop.


Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.


Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. 
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.




Theorem add_0_r_firsttry : forall (n : nat),
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    intros m.
    simpl.
    rewrite -> add_0_r_firsttry.
    reflexivity.
  - simpl.
    intros m.
    rewrite <- plus_n_Sm.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.

Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct n eqn:E.
    + reflexivity.
    + simpl in H.
      discriminate H.
  - destruct m eqn:E.
    + reflexivity.
    + rewrite -> add_comm in H.
      simpl in H.
      discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. 
Qed.

Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

(* /\ notation for : *)
Check and : Prop -> Prop -> Prop.




Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma factor_is_O':
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [ Hn | Hm ] eqn:E.
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.


Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma or_intro_r : forall A B : Prop, B -> A \/ B.
Proof.
  intros A B HB.
  right.
  apply HB.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.
Definition not (P: Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not : Prop -> Prop.

Theorem tst: not (2 + 2 = 5).
Proof.
  intros H.
  simpl in H.
  discriminate H.
Qed.

Theorem tst': not (2 + 2 = 4).
Proof.
  intros H.
  simpl in H.
  (* discriminate H. *)
Abort.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop), False -> P.
Proof.
  intros P contra.
  destruct contra. 
Qed.

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P notP Q p.
  destruct (notP p) eqn:E.
Qed.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False : ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. 
  unfold not in HNA.
  apply HNA in HP. 
  destruct HP. 
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. 
  unfold not. 
  intros G. 
  apply G. 
  apply H. 
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros negQ p.
  apply H in p.
  apply negQ in p.
  apply p.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros [ HP HnP ].
  apply HnP in HP.
  destruct HP.
Qed.


Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== replaces target with False *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* Search (?X : True). *)

Lemma True_is_true : True.
Proof. apply I. Qed.


Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc : forall n, ~ (O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.







Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.


Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. 
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros H.
    destruct H as [ HP | [HQ HR] ] eqn:E.
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [HPQ HPR].
    destruct HPQ as [HP | HQ] eqn:E.
    + left. apply HP.
    + destruct HPR as [HP' | HR] eqn:E1.
      * left. apply HP'.
      * right.
        split.
        apply HQ.
        apply HR.
Qed.



From Coq Require Import Setoids.Setoid.

Theorem mult_is_O : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [| n' ] [| m' ] H.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - simpl in H.
    discriminate H.
Qed.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.


Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.


Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Fixpoint even (n : nat) : bool :=
  match n with 
  | O => true
  | S O => false
  | S (S m) => even m
  end.
Definition odd (n : nat) := negb (even n).

(* Definition div2 (n: nat) (p: even n = true) : nat. *)



Definition Even x := exists n : nat, x = double n.

Lemma four_is_even : Even 4.
Proof.
  unfold Even. 
  exists 2. 
  reflexivity.
Qed.

Theorem tst_exists: forall (n: nat), even n = true -> exists (m : nat), double m = n.
Proof.
  intros n H.

Abort.


Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. (* note implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x Px].
  apply Px.
  apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [Px | Qx]].
    + left. exists x. apply Px.
    + right. exists x. apply Qx.
  - intros [ [x Px] | [x Qx] ].
    + exists x. left. apply Px.
    + exists x. right. apply Qx.
Qed.



Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | nil      => False
  | cons h t => h = x \/ In x t
  end.

Definition tst_list : list nat := cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))).

Example In_example_1 : @In nat 4 tst_list.
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.


Example In_example_2 :
  forall n, In n (cons 2 (cons 4 nil)) ->
  exists n', n = 2 * n'.
Proof.
  intros n H.
  simpl in H.
  destruct H as [H'2 | [H'4 | H'n]].
  - exists 1.
    rewrite <- H'2.
    reflexivity.
  - exists 2.
    rewrite <- H'4.
    reflexivity.
  - destruct H'n.
Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | nil      => nil
  | cons h t => cons (f h) (map f t)
  end.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x H.
  induction l as [| hl tl Hl ].
  - simpl in H.
    simpl.
    apply H.
  - simpl in H. 
    simpl.
    destruct H as [H'l | H'r].
    + rewrite -> H'l.
      left.
      reflexivity.
    + right.
      apply Hl.
      apply H'r.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. 
  split.
  - induction l as [| hl tl Hl ].
    + simpl.
      intros F.
      destruct F.
    + simpl.
      intros [H'l | H'r].
      * exists hl.
        split.
        -- apply H'l.
        -- left. reflexivity.
      * destruct (Hl H'r) as [x [Hfxy HInxtl]].
        -- exists x.
           split.
            ++ apply Hfxy.
            ++ right. apply HInxtl.
  - intros [x [ Hfxy Hinxl ]].
    induction l as [| hl tl Hl ].
    + simpl.
      simpl in Hinxl.
      apply Hinxl.
    + simpl.
      simpl in Hinxl.
      destruct Hinxl as [Hhlx | Hinxtl].
      * rewrite <- Hhlx in Hfxy.
        left. apply Hfxy.
      * right.
        apply Hl.
        apply Hinxtl.
Qed.

Theorem In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l.
  induction l as [| hl tl Hl ].
  - simpl.
    split.
    + intros H. right. apply H.
    + intros [FH | H]. 
      * destruct FH.
      * apply H.
  - simpl.
    intros l' a.
    rewrite -> (Hl l' a).
    apply or_assoc.
Qed.


Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | nil      => True
  | cons h t => P h /\ All P t
  end.

Theorem All_In : forall (T : Type) (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  induction l as [| hl tl Hl ].
  - simpl.
    split.
    + intros H. apply I.
    + intros H x FH. exfalso. apply FH.
  - simpl.
    split.
    + intros H.
      split.
      * apply H. left. reflexivity.
      * apply Hl. intros x H'. apply (H x). right. apply H'.
    + intros [Hphl Hallptl] x H.
      destruct Hl as [Hll Hlr].
      destruct H as [Hl | Hr].
      * rewrite <- Hl. apply Hphl.
      * apply Hlr. apply Hallptl. apply Hr.
Qed.


Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if odd n then Podd n else Peven n.


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  destruct (odd n) eqn:E.
  - unfold combine_odd_even.
    rewrite -> E.
    apply H1.
    reflexivity.
  - unfold combine_odd_even.
    rewrite -> E.
    apply H2.
    reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  intros H G.
  rewrite -> G in H.
  simpl in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  intros H G.
  rewrite -> G in H.
  simpl in H.
  apply H.
Qed.



Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> nil.
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> nil.
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall (l : list nat), In 42 l -> l <> nil.
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.


Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' H].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.
















Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.


Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. 
  intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2. 



Fixpoint rev {X} (l : list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => rev t ++ cons h nil
  end.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => rev_append t (cons h l2)
  end.
Definition tr_rev {X} (l : list X) : list X := rev_append l nil.


Lemma list_plus_nil : forall (X : Type) (l : list X),
  (l ++ nil = l)%list.
Proof.
  intros X l.
  induction l as [| hl tl Hl ].
  - reflexivity.
  - simpl.
    rewrite -> Hl.
    reflexivity.
Qed.

Lemma rev_append_t : forall (X : Type) (l1 l2 l3 : list X), 
  ((@rev_append X l1 l2) ++ l3 = @rev_append X l1 (l2 ++ l3))%list.
Proof.
  intros X l1 l2 l3.
  induction l3 as [| hl tl Hl ].
  - simpl.
    rewrite -> list_plus_nil.
    rewrite -> list_plus_nil.
    reflexivity.
  - simpl.
Abort.

Lemma rev_append_t1 : forall (X : Type) (l1 l2 : list X), 
  (rev_append l1 nil ++ l2 = rev_append l1 l2)%list.
Proof.
  intros X l1 l2.
  induction l1 as [| hl tl Hl ].
  - reflexivity.
  - Abort.

Lemma app_assoc : forall (X : Type) (l1 l2 l3 : list X),
  ((l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3))%list.
Proof.
  induction l1 as [| hl tl Hl ].
  - reflexivity.
  - simpl.
    intros l2 l3.
    rewrite <- Hl.
    reflexivity.
Qed.
    
Lemma rev_append_t3 : forall (X : Type) (l1 l2 : list X), 
  (rev_append l1 l2 = (rev_append l1 nil) ++ l2)%list.
Proof.
  intros X l1.
  induction l1 as [| hl tl Hl ].
  - reflexivity.
  - simpl.
    intros l2.
    rewrite -> Hl.
    rewrite -> (Hl (cons hl nil)).
    rewrite -> app_assoc.
    simpl.
    reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l.
  induction l as [| hl tl Hl ].
  - unfold tr_rev.
    reflexivity.
  - unfold tr_rev.
    simpl.
    rewrite <- Hl.
    unfold tr_rev.
    rewrite -> rev_append_t3.
    reflexivity.
Qed.








Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma even_S : forall n, even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' Hn ].
  - reflexivity.
  - rewrite -> Hn.
    simpl.
    destruct (even n').
    + reflexivity.
    + reflexivity.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n as [| n' Hn ].
  - simpl.
    exists O.
    reflexivity.
  - rewrite -> even_S.
    destruct Hn as [k Hn'].
    destruct (even n').
    + simpl.
      exists k.
      rewrite -> Hn'.
      reflexivity.
    + simpl.
      rewrite -> Hn'.
      exists (S k).
      reflexivity.
Qed.

Lemma even_double_true : forall n, even (double n) = true.
Proof.
  intros n.
  induction n as [| n' H ].
  - reflexivity.
  - simpl.
    apply H.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n.
  split.
  - intros H.
    unfold Even.
    destruct (even_double_conv n) as [k Hd].
    rewrite -> H in Hd.
    exists k.
    apply Hd.
  - unfold Even.
    intros [k H].
    rewrite -> H.
    apply even_double_true.
Qed.



Example even_1000 : Even 1000.
Proof. unfold Even. exists 500. reflexivity. Qed.

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.


Theorem andb_true_iff : forall (b1 b2 : bool),
  andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  destruct b1 eqn:E1.
  - destruct b2 eqn:E2.
    + simpl. 
      split. 
      * intros H.
        split.
        -- reflexivity.
        -- reflexivity.
      * intros [H1 H2].
        reflexivity.
    + simpl.
      split.
      * intros H.
        split.
        -- reflexivity.
        -- apply H.
      * intros [H1 H2].
        apply H2.
  - simpl.
    split.
    + intros H.
      discriminate H.
    + intros [H1 H2].
      discriminate H1.
Qed.

Theorem orb_true_iff : forall (b1 b2 : bool),
  orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  destruct b1 eqn:E.
  - simpl.
    split.
    + intros H. left. reflexivity.
    + intros H. reflexivity.
  - destruct b2.
    + simpl.
      split.
      * intros H. right. reflexivity.
      * intros H. reflexivity.
    + simpl.
      split.
      * intros H. discriminate H.
      * intros [H1|H2]. discriminate H1. discriminate H2.
Qed.


Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => eqb i j
  | _, _ => false
  end.
Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => leb i j
  | O, S _ => true
  | _, _ => false
  end.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Lemma eqb_refl : forall (n : nat), n =? n = true.
Proof.
  intros n.
  induction n as [| n' H ].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' H].
  - intros m.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + simpl.
      intros G.
      discriminate G.
  - intros m.
    destruct m as [| m'] eqn:E.
    + simpl.
      intros G.
      discriminate G.
    + simpl.
      intros G.
      apply f_equal.
      apply H.
      apply G.
Qed.

Theorem eqb_neq : forall (x y : nat),
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  split.
  - unfold not.
    intros H G.
    rewrite -> G in H.
    simpl in H.
    rewrite -> eqb_refl in H.
    discriminate H.
  - unfold not.
    intros H.
    destruct (x =? y) eqn:E.
    + destruct (H (eqb_true x y E)) eqn:G.
    + reflexivity.
Qed.


Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | (cons h1 t1), (cons h2 t2) => if eqb h1 h2 then eqb_list eqb t1 t2 else false
  | _, _ => false
  end.

Lemma eqb_list_refl : forall (A : Type) (eqb : A -> A -> bool) (l : list A),
  (forall a, eqb a a = true) ->
  eqb_list eqb l l = true.
Proof.
  intros A eqb l HEq.
  induction l as [| hl tl Hl ].
  - reflexivity.
  - simpl.
    rewrite -> HEq.
    apply Hl.
Qed.


Theorem eqb_list_true_iff :
  forall (A : Type) (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H.
  split.
  - generalize dependent l2.
    induction l1 as [| hl tl Hl ].
    + simpl.
      destruct l2.
      * intros _. reflexivity.
      * intros F. discriminate F.
    + intros l2 Heqlist.
      simpl in Heqlist.
      destruct l2 as [|hl2 tl2 ] eqn:E.
      * discriminate Heqlist.
      * destruct (eqb hl hl2) eqn:Ehla.
        -- destruct (H hl hl2) as [H' _].
           destruct (H' Ehla).
           destruct (Hl tl2 Heqlist).
           reflexivity.
        -- discriminate Heqlist.
  - intros HLEq.
    rewrite -> HLEq.
    apply eqb_list_refl.
    intros a.
    destruct (H a a) as [_ H'].
    apply H'.
    reflexivity.
Qed.




Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil      => true
  | cons h t => andb (test h) (forallb test t)
  end.

Lemma andb_split : forall (a b : bool), andb a b = true -> a = true /\ b = true.
Proof.
  intros a b.
  destruct a eqn:EA.
  - destruct b eqn:EB.
    + simpl. intros H. split. reflexivity. reflexivity.
    + simpl. intros H. discriminate H.
  - simpl. intros H. discriminate H.
Qed.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  split.
  - intros H.
    induction l as [| hl tl Hl ].
    + reflexivity.
    + simpl. simpl in H.
      destruct (andb_split (test hl) (forallb test tl) H) as [H1 H2].
      split.
      * apply H1.
      * apply Hl. apply H2.
  - intros H.
    induction l as [| hl tl Hl ].
    + reflexivity.
    + simpl. simpl in H.
      destruct H as [H1 H2].
      rewrite -> (Hl H2).
      rewrite -> H1.
      reflexivity.
Qed.





Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(*
Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.

  assert (G: forall b, b = true \/ ~ (b = true)). {
    intros b.
    destruct b.
    - left. reflexivity.
    - right. unfold not. intros H'. discriminate H'.
  }

  destruct (H (G true)).
  
  apply H.
  apply G.
*)

Definition excluded_middle := forall P : Prop, P \/ ~P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~(exists x, ~ P x) -> (forall x, P x).
Proof.
  intros ExclMid X P.
  intros H x.
  unfold not in H.
  destruct (ExclMid (P x)) as [HPx | HNPx].
  - apply HPx.
  - assert(E: (exists x : X, P x -> False)). {
      exists x.
      apply HNPx.
    }
    destruct (H E).
Qed.








Definition peirce := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P:Prop, ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop, (P -> Q) -> (~P \/ Q).

(* Coq'Art book by Bertot and Casteran (p. 123). *)
(*
Theorem th1 : excluded_middle <-> peirce.
Theorem th2 : peirce <-> double_negation_elimination.
Theorem th3 : double_negation_elimination <-> de_morgan_not_and_not.
Theorem th4 : de_morgan_not_and_not <-> implies_to_or.
Theorem th5 : implies_to_or <-> excluded_middle.
*)
End Logic.
