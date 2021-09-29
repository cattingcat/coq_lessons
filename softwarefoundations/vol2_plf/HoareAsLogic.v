Set Warnings "-deprecated-hint-without-locality,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Hoare.
Hint Constructors ceval : core.


Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable (Q [V |-> a]) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable P c Q -> derivable Q d R -> derivable P <{c;d}> R
  | H_If : forall P Q (b: bexp) c1 c2,
    derivable (P /\  b) c1 Q ->
    derivable (P /\ ~b) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P (b: bexp) c,
    derivable (P /\ b) c P ->
    derivable P <{while b do c end}> (P /\ ~b)
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (P ->> P') ->
    (Q' ->> Q) ->
    derivable P c Q.

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (P ->> P') ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Lemma H_Consequence_post : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (Q' ->> Q) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Example sample_proof :
  derivable
    ((assert (X = 3)) [X |-> X + 2] [X |-> X + 1])
    <{ X := X + 1; X := X + 2}>
    (assert (X = 3)).
Proof.
  eapply H_Seq.
  - apply H_Asgn.
  - apply H_Asgn.
Qed.

Theorem provable_true_post : forall c P,
    derivable P c True.
Proof.
  intro c.
  induction c; intro P.
  - eapply H_Consequence_post.
    eapply (H_Skip).
    auto.
  - eapply H_Consequence_pre.
    eapply (H_Asgn).
    auto.
  - eapply (H_Seq).
    apply IHc1.
    apply IHc2.
  - apply H_If.
    apply IHc1.
    apply IHc2.
  - eapply H_Consequence.
    eapply H_While.
    apply IHc.
    auto. auto.
Qed.


Lemma false_assrt: forall Q, False ->> Q.
Proof. intros Q st F. simpl in F. destruct F. Qed.

Theorem provable_false_pre : forall c Q,
    derivable False c Q.
Proof.
  intro c.
  induction c; intro Q.
  - eapply H_Consequence_pre.
    eapply (H_Skip).
    apply false_assrt.
  - eapply H_Consequence_pre.
    eapply (H_Asgn).
    apply false_assrt.
  - eapply (H_Seq).
    apply IHc1.
    apply IHc2.
  - eapply H_If.
    + eapply H_Consequence_pre.
      apply IHc1. simpl.
      intros st [F _]. apply F.
    + eapply H_Consequence_pre.
      apply IHc2. simpl.
      intros st [F _]. apply F.
  - eapply H_Consequence.
    + eapply H_While.
      eapply H_Consequence_pre.
      eapply IHc.
      intros st [F _]. apply F.
    + apply false_assrt.
    + simpl. intros st [F _]. destruct F.
Qed.


Theorem hoare_sound : forall P c Q,
  derivable P c Q -> {{P}} c {{Q}}.
Proof.
  intros P c Q Hder.
  induction Hder; intros st st' com Hp.
  - inversion com; subst. assumption.
  - inversion com; subst. unfold assn_sub in Hp. assumption.
  - inversion com; subst.
    eapply IHHder2. apply H4.
    eapply IHHder1. apply H1.
    apply Hp.
  - inversion com; subst.
    + (* if true *)
      eapply IHHder1. apply H5.
      split. apply Hp. apply H4.
    + (* if false *)
      eapply IHHder2. apply H5.
      split. apply Hp. simpl. intro Contra. congruence.
  - remember <{ while b do c end }> as k eqn:Ek.
    induction com; try (discriminate Ek).
    + injection Ek as Ek1 Ek2. subst. split.
      * assumption.
      * intro Contra. congruence.
    + injection Ek as Ek1 Ek2. subst.
      apply IHcom2; try reflexivity.
      eapply IHHder.
      apply com1.
      split.
      * assumption.
      * apply H.
  - apply a0.
    eapply IHHder.
    apply com.
    apply a.
    assumption.
Qed.



(* Weakest precondifiton for Q *)
Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.
Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q,
  {{wp c Q}} c {{Q}}.
Proof. intros c Q st st' com. unfold wp. intro H. auto. Qed.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} -> P' ->> (wp c Q).
Proof. eauto. Qed.


Lemma wp_seq : forall P Q c1 c2,
    derivable P c1 (wp c2 Q) -> derivable (wp c2 Q) c2 Q -> derivable P <{c1; c2}> Q.
Proof.
  intros P Q c1 c2 H1 H2.
  eapply H_Seq.
  apply H1.
  apply H2.
Qed.

Lemma wp_invariant : forall b c Q,
    hoare_triple (wp <{while b do c end}> Q /\ b) c (wp <{while b do c end}> Q).
Proof.
  intros b c Q st st' com [H1 H2].
  unfold wp in *.
  intros s' comWhile.
  apply H1.
  eapply E_WhileTrue.
  - apply H2.
  - apply com.
  - apply comWhile.
Qed.

(*
Lemma split_seq: forall P Q c1 c2, 
  {{P}} c1; c2 {{Q}} -> {{wp c2 Q}} c2 {{Q}} /\ {{P}} c1 {{wp c2 Q}}.
Proof.
  intros P Q c1 c2 H.
  unfold hoare_triple in H.
  split.
  - intros st' st'' comC2 Hwp. 
    eapply (H).
    eapply E_Seq.
*)

Theorem hoare_complete: forall P c Q,
  {{P}} c {{Q}} -> derivable P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - (* skip *)
    eapply H_Consequence_post.
    apply H_Skip.
    intros st Hpst.
    unfold hoare_triple in HT.
    apply (HT st st).
    + apply E_Skip.
    + assumption.
  - (* assign *)
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros st Hpst.
    unfold hoare_triple in HT.
    apply (HT st).
    + apply E_Asgn.
      reflexivity.
    + assumption.
  - (* seq *)
    apply wp_seq.
    + apply IHc1.
      unfold hoare_triple in HT.
      intros st st' comC1 Hpst. unfold wp.
      intros s' comC2.
      eapply HT.
      eapply E_Seq.
      apply comC1.
      apply comC2.
      apply Hpst.
    + apply IHc2.
      unfold hoare_triple in HT.
      intros st st' comC2 Hwp.
      apply Hwp.
      apply comC2.
  - (* if *)
    apply H_If.
    + (* true *)
      apply IHc1.
      intros st st' comC1 [Hpst Hb].
      eapply HT.
      apply E_IfTrue.
      apply Hb.
      apply comC1.
      apply Hpst.
    + (* false *)
      apply IHc2.
      intros st st' comC1 [Hpst Hnotb].
      eapply HT.
      apply E_IfFalse.
      assert (G: beval st b = false). {
        destruct (beval st b) eqn:Hb.
        * exfalso. apply Hnotb. apply Hb.
        * reflexivity.
      }
      apply G.
      apply comC1.
      apply Hpst.
  - (* while *)
    eapply H_Consequence.
    + eapply H_While.
      apply IHc.
      apply wp_invariant.
    + apply wp_is_weakest.
      apply HT.
    + intros st [H1 H2].
      apply H1.
      apply E_WhileFalse.
      assert (G: beval st b = false). {
        destruct (beval st b) eqn:Hb.
        * exfalso. apply H2. apply Hb.
        * reflexivity.
      }
      apply G.
Qed.
