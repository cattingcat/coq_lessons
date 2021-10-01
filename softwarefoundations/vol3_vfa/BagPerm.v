From Coq Require Import Strings.String.
From Coq Require Import Setoid Morphisms.
From VFA Require Import Perm.
From VFA Require Import Sort.

Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil     => 0
  | h :: t  =>
      (if h =? v then 1 else 0) + count v t
  end.

Definition bag_eqv (b1 b2: bag) : Prop :=
  forall n, count n b1 = count n b2.

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof.
  intros b n.
  reflexivity.
Qed.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1.
Proof.
  intros b1 b2 H n.
  rewrite (H n).
  reflexivity.
Qed.

Lemma bag_eqv_trans: forall b1 b2 b3, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof.
  intros b1 b2 b3 H1 H2 n.
  rewrite (H1 n).
  rewrite (H2 n).
  reflexivity.
Qed.

Lemma bag_eqv_cons : forall x b1 b2, bag_eqv b1 b2 -> bag_eqv (x::b1) (x::b2).
Proof.
  intros x b1 b2 H n.
  simpl.
  rewrite (H n).
  reflexivity.
Qed.



Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, bag_eqv al (f al) /\ sorted (f al).


Lemma insert_bag: forall x l, bag_eqv (x :: l) (insert x l).
Proof.
  intros x l.
  induction l; intros n.
  - simpl. reflexivity.
  - apply (bag_eqv_cons a) in IHl.
    simpl.
    bdestruct (a >=? x).
    + reflexivity.
    + rewrite <- (IHl).
      simpl. lia.
Qed.

Theorem sort_bag: forall l, bag_eqv l (sort l).
Proof.
  intro l.
  induction l; intro n.
  - reflexivity.
  - simpl. 
    rewrite <- insert_bag.
    simpl.
    rewrite <- (IHl n).
    reflexivity.
Qed.

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
  split. apply sort_bag. apply sort_sorted.
Qed.


Search Permutation.
Print Permutation.
Search (?a =? ?a).
Search (?a <> ?x -> ?a =? ?x = false).

Lemma perm_bag: forall al bl : list nat,
   Permutation al bl -> bag_eqv al bl.
Proof.
  intros al bl H n.
  induction H.
  - reflexivity.
  - simpl. rewrite IHPermutation. reflexivity.
  - simpl. lia.
  - rewrite IHPermutation1, IHPermutation2.
    reflexivity.
Qed.

Lemma bag_nil_inv : forall b, bag_eqv [] b -> b = [].
Proof.
  intros b.
  induction b; simpl; intro H.
  - reflexivity.
  - exfalso.
    specialize (H a).
    simpl in H.
    rewrite -> Nat.eqb_refl in H.
    discriminate H.
Qed.

Lemma bag_cons_inv : forall l x n,
    S n = count x l ->
    exists l1 l2, l = l1 ++ x :: l2 /\ count x (l1 ++ l2) = n.
Proof.
  intro l.
  induction l; simpl; intros x n Hcount.
  - discriminate Hcount.
  - bdestruct (a =? x); subst.
    + exists nil, l.
      split; 
        try reflexivity; 
        try (simpl; lia).
    + simpl in Hcount.
      destruct (IHl x n Hcount) as [l1 [l2 [ Heq Hcnt]]].
      exists (a :: l1), l2.
      split.
      * simpl. rewrite <- Heq. reflexivity.
      * simpl. rewrite Hcnt.
        assert (G: a =? x = false). {
          bdestruct (a =? x); subst.
          - exfalso. apply H. reflexivity.
          - reflexivity.
        }
        rewrite G. reflexivity.
Qed.

Lemma count_distr: forall l1 l2 x, 
  count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
  intro l1.
  induction l1; simpl; intros l2 x.
  - reflexivity.
  - bdestruct (a =? x); rewrite IHl1; lia.
Qed.

Lemma count_insert_other : forall l1 l2 x y,
    y <> x -> count y (l1 ++ x :: l2) = count y (l1 ++ l2).
Proof.
  intros l1 l2 x y Hneq.
  change (l1 ++ x :: l2) with (l1 ++ [x] ++ l2).
  repeat (rewrite count_distr).
  assert (G: count y [x] = 0). {
    simpl. bdestruct (x =? y).
    - exfalso. apply Hneq. symmetry. assumption.
    - reflexivity.
  }
  rewrite G. lia.
Qed.

Lemma bag_perm: forall al bl, 
  bag_eqv al bl -> Permutation al bl.
Proof.
  intros al.
  induction al; simpl; intros bl H.
  - apply bag_nil_inv in H. subst. constructor.
  - assert (G: exists l1 l2, bl = l1 ++ a :: l2 /\ count a (l1 ++ l2) = count a al). {
      specialize (H a). simpl in H. rewrite -> Nat.eqb_refl in H. simpl in H.
      apply bag_cons_inv in H.
      assumption.
    }
    destruct G as [l1 [l2 [ Heq Hcnt]]].
    subst.
    apply perm_trans with (a :: (l1 ++ l2)).
    + apply perm_skip.
      apply IHal.
      intro n.
      specialize (H n).
      rewrite count_distr in *.
      simpl in H.
      bdestruct (a =? n); lia.
    + change (a :: l1 ++ l2) with ([a] ++ l1 ++ l2).
      change (l1 ++ a :: l2) with (l1 ++ [a] ++ l2).
      rewrite (app_assoc l1 [a]).
      rewrite (Permutation_app_comm l1 [a]).
      rewrite (app_assoc).
      apply Permutation_refl.
Qed.


Theorem bag_eqv_iff_perm:  forall al bl, 
  bag_eqv al bl <-> Permutation al bl.
Proof.
  intros. split. 
  - apply bag_perm. 
  - apply perm_bag.
Qed.

Corollary sort_specifications_equivalent: forall sort, 
  is_a_sorting_algorithm sort <-> is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply bag_eqv_iff_perm; auto.
Qed.
