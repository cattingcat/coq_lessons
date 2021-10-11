From VFA Require Import Perm.

Module Type PRIQUEUE.
  Parameter priqueue: Type.
  Definition key := nat.
  Parameter empty: priqueue.
  Parameter insert: key -> priqueue -> priqueue.
  Parameter delete_max: priqueue -> option (key * priqueue).
  Parameter merge: priqueue -> priqueue -> priqueue.

  Parameter priq: priqueue -> Prop.
  Parameter Abs: priqueue -> list key -> Prop.

  Axiom can_relate: forall p, priq p -> exists al, Abs p al.
  Axiom abs_perm: forall p al bl,
   priq p -> Abs p al -> Abs p bl -> Permutation al bl.
  Axiom empty_priq: priq empty.
  Axiom empty_relate: Abs empty nil.
  Axiom insert_priq: forall k p, priq p -> priq (insert k p).
  Axiom insert_relate:
        forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
  Axiom delete_max_None_relate:
        forall p, priq p -> (Abs p nil <-> delete_max p = None).
  Axiom delete_max_Some_priq:
      forall p q k, priq p -> delete_max p = Some(k,q) -> priq q.
  Axiom delete_max_Some_relate:
  forall (p q: priqueue) k (pl ql: list key), priq p ->
   Abs p pl ->
   delete_max p = Some (k,q) ->
   Abs q ql ->
   Permutation pl (k::ql) /\ Forall (ge k) ql.
  Axiom merge_priq: forall p q, priq p -> priq q -> priq (merge p q).
  Axiom merge_relate:
    forall p q pl ql al,
       priq p -> priq q ->
       Abs p pl -> Abs q ql -> Abs (merge p q) al ->
       Permutation al (pl++ql).
End PRIQUEUE.



Module List_Priqueue <: PRIQUEUE.

  Fixpoint select (i: nat) (l: list nat) : (nat * list nat) :=
  match l with
  | nil    => (i, nil)
  | h :: t => if i >=? h
                 then let (j, l') := select i t in (j, h::l')
                 else let (j, l') := select h t in (j, i::l')
  end.

  Lemma select_perm: forall i l,
    let (j,r) := select i l in Permutation (i::l) (j::r).
  Proof.
  intros i l; revert i.
  induction l; intros; simpl in *.
  - constructor.
    constructor.
  - bdestruct (i >=? a).
    + destruct (select i l) eqn:E.
      change (i :: a :: l) with ([i] ++ [a] ++ l).
      change (n :: a :: l0) with ([n] ++ [a] ++ l0).
      apply perm_trans with ([a] ++ [i] ++ l).
      * apply Permutation_app_swap_app.
      * apply perm_trans with ([a] ++ [n] ++ l0).
        ** simpl. 
           apply perm_skip.
           specialize (IHl i).
           rewrite E in IHl.
           apply IHl.
        ** apply Permutation_app_swap_app.
    + destruct (select a l) eqn:E.
           specialize (IHl a).
           rewrite E in IHl.
      change (n :: i :: l0) with ([n] ++ [i] ++ l0).
      apply perm_trans with ([i] ++ [n] ++ l0).
      * simpl.
        apply perm_skip.
        apply IHl.
      * apply Permutation_app_swap_app.
  Qed.

  Lemma select_biggest_aux: forall i al j bl,
      Forall (fun x => j >= x) bl ->
      select i al = (j, bl) ->
      j >= i.
  Proof.
    intros i al. revert i.
    induction al; simpl; intros i j bl Hall H.
    - injection H as Hl Hr; subst.
      lia.
    - bdestruct (i >=? a).
      + destruct (select i al) eqn:E.
        injection H as Hl Hr; subst.
        inversion Hall; subst.
        eapply IHal.
          apply H3.
          apply E.
      + destruct (select a al) eqn:E.
        injection H as Hl Hr; subst.
        inversion Hall; subst.
        assumption.
  Qed.

  Theorem select_biggest: forall i al j bl, 
    select i al = (j, bl) ->
    Forall (fun x => j >= x) bl.
  Proof.
    intros i al; revert i; induction al; intros; simpl in *.
    - injection H as ? ?; subst.
      constructor.
    - bdestruct (i >=? a).
      + destruct (select i al) eqn:E.
        injection H as ? ?; subst.
        constructor.
        * assert (G: j >= i). {
            eapply select_biggest_aux.
            eapply IHal.
            apply E.
            apply E.
          }
          lia.
        * eapply IHal.
          apply E.
      + destruct (select a al) eqn:E.
        injection H as ? ?; subst.
        constructor.
        * assert (G: j >= a). {
            eapply select_biggest_aux.
            eapply IHal.
            apply E.
            apply E.
          }
          lia.
        * eapply IHal.
          apply E.
  Qed.

  Definition key := nat.
  Definition priqueue := list key.
  Definition empty : priqueue := nil.
  Definition insert (k: key) (p: priqueue) := k :: p.
  Definition delete_max (p: priqueue) :=
    match p with
    | nil     => None
    | i :: p' => Some (select i p')
    end.
  Definition merge (p q: priqueue) : priqueue := p ++ q.

  Definition priq (p: priqueue) := True.

  Inductive Abs': priqueue -> list key -> Prop :=
    | Abs_intro: forall p, Abs' p p.

  Definition Abs := Abs'.

  Lemma can_relate : forall p, priq p -> exists al, Abs p al.
  Proof.
    intros. exists p; constructor.
  Qed.

  Lemma delete_max_None_relate: forall p, 
        priq p ->
        (Abs p nil <-> delete_max p = None).
  Proof.
    intros. split; intros.
    - inversion H0; subst. reflexivity.
    - unfold delete_max in *.
      destruct p.
      + constructor.
      + discriminate.
  Qed.

  Lemma delete_max_Some_relate: forall (p q: priqueue) k (pl ql: list key), 
     priq p ->
     Abs p pl ->
     delete_max p = Some (k,q) ->
     Abs q ql ->
     Permutation pl (k::ql) /\ Forall (ge k) ql.
  Proof.
    intros.
    clear H.
    inversion H0; subst. inversion H2; subst. clear H0 H2.
    unfold delete_max in *.
    destruct pl; try discriminate.
    injection H1 as H1.
    split.
    - assert (G: let (k, ql) := select k0 pl in Permutation (k0 :: pl) (k :: ql)). {
        apply select_perm.
      }
      rewrite H1 in G.
      assumption.
    - eapply select_biggest.
      apply H1.
  Qed.

  Lemma merge_priq: forall p q, 
    priq p -> priq q -> priq (merge p q).
  Proof. intros. constructor. Qed.

  Lemma merge_relate: forall p q pl ql al,
         priq p -> priq q ->
         Abs p pl -> Abs q ql -> Abs (merge p q) al ->
         Permutation al (pl ++ ql).
  Proof.
    intros.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    unfold merge.
    apply Permutation_refl.
  Qed.

  Lemma abs_perm: forall p al bl,
    priq p -> Abs p al -> Abs p bl -> Permutation al bl.
  Proof.
    intros.
    inv H0. inv H1. apply Permutation_refl.
  Qed.


  Lemma empty_priq: priq empty.
  Proof. constructor. Qed.

  Lemma empty_relate: Abs empty nil.
  Proof. constructor. Qed.

  Lemma insert_priq: forall k p, priq p -> priq (insert k p).
  Proof. intros; constructor. Qed.

  Lemma insert_relate: forall p al k, 
    priq p -> Abs p al -> Abs (insert k p) (k :: al).
  Proof. intros. unfold insert. inv H0. constructor. Qed.

  Lemma delete_max_Some_priq: forall p q k, 
    priq p -> delete_max p = Some(k, q) -> priq q.
  Proof. constructor. Qed.

End List_Priqueue.
