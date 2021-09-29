Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.


Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | []      => [i]
  | h :: t  => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | []      => []
  | h :: t  => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.



Inductive sorted : list nat -> Prop :=
| sorted_nil  : sorted []
| sorted_1    : forall x, sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition sorted'' (al : list nat) := forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.



Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).




Notation  "a >=? b" := (Nat.leb b a)
                          (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a)
                         (at level 70) : nat_scope.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].



Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. 
  induction S; simpl.
  - constructor.
  - bdestruct (a <=? x).
    + apply sorted_cons.
        assumption.
        constructor.
    + apply sorted_cons.
        lia.
        constructor.
  - bdestruct (x >=? a).
    + apply sorted_cons; try lia.
      apply sorted_cons; try lia.
      assumption.
    + simpl in IHS.
      bdestruct (y >=? a).
      * apply sorted_cons; try lia.
        assumption.
      * apply sorted_cons; try lia.
        assumption.
Qed.

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  intro l.
  induction l; simpl.
  - constructor.
  - apply insert_sorted.
    assumption.
Qed.

Print Permutation.
Search Permutation.

Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  intros x l.
  induction l; simpl.
  - constructor. constructor.
  - bdestruct (a >=? x).
    + apply Permutation_refl.
    + apply perm_trans with (a :: x :: l).
      * apply perm_swap.
      * constructor.
        assumption.
Qed.

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intro l.
  induction l; simpl.
  - constructor.
  - apply perm_trans with (a :: sort l).
    + constructor. assumption.
    + apply insert_perm.
Qed.

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.



Lemma less_than_all_sorted: forall x y l,
  x <= y -> sorted' (y :: l) -> 
  forall i iv, nth_error (y :: l) i = Some iv -> x <= iv.
Proof.
  intros x y l Hxy Hsorted.
  unfold sorted' in Hsorted.
  intro i.
  induction i.
  - simpl. intros iv H'. injection H' as H'.
    subst. assumption.
  - simpl. intros iv H'.
    assert (y <= iv). {
      apply (Hsorted 0 (S i) y iv).
      + lia.
      + reflexivity.
      + simpl. apply H'.
    }
    lia.
Qed.

Lemma sorted_sorted': forall al, sorted al -> sorted' al.
Proof.
  intros al.
  induction al; simpl; intro Hsorted.
  - intros i j iv jv Hind H1 H2.
    destruct i; simpl in H1; discriminate H1.
  - inversion Hsorted; subst.
    + intros i j iv jv Hind H1 H2.
      destruct i; inversion Hind; subst.
      -- discriminate H2.
      -- simpl in H2.
         destruct m; simpl in H2; discriminate H2.
      -- discriminate H2.
      -- simpl in H2.
         destruct m; simpl in H2; discriminate H2.
    + intros i j iv jv Hind H1' H2'.
      destruct i; destruct j.
      * lia.
      * apply IHal in H2. clear IHal.
        simpl in H1', H2'.
        injection H1' as H1'; subst.
        induction j.
        -- simpl in H2'. injection H2' as H2'; subst.
           assumption.
        -- apply (less_than_all_sorted _ _ _ H1 H2  (S j) jv H2').
      * lia.
      * simpl in H1', H2'.
        apply (IHal H2 i j iv jv).
        -- lia.
        -- apply H1'.
        -- apply H2'.
Qed.

Lemma sorted_tail: 
  forall a l, sorted' (a :: l) -> sorted' l.
Proof.
  intros a l H i j iv jv Hilj Hiv Hjv.
  apply (H (S i) (S j) iv jv).
  - lia.
  - simpl. apply Hiv.
  - simpl. apply Hjv.
Qed.

Lemma sorted'_sorted : forall al, sorted' al -> sorted al.
Proof.
  intro al.
  induction al.
  - intro H. constructor.
  - intro H.
    destruct al as [ | alh alt].
    + constructor.
    + apply sorted_cons.
      * unfold sorted' in H.
        apply (H 0 1).
          lia.
          reflexivity.
          reflexivity.
      * apply IHal.
        apply sorted_tail with a.
        apply H.
Qed.


Lemma nth_error_insert : forall l a i iv,
    nth_error (insert a l) i = Some iv ->
    a = iv \/ exists i', nth_error l i' = Some iv.
Proof.
  intro l.
  induction l; simpl; intros a' i iv H.
  - destruct i; try (destruct i; discriminate H).
    simpl in H. injection H as H.
    left.
    assumption.
  - bdestruct (a >=? a').
    + destruct i.
      * simpl in H. injection H as H.
        left.
        assumption.
      * simpl in H.
        right. exists i. apply H.
    + destruct i.
      * simpl in H. injection H as H. subst.
        right.
        exists 0. reflexivity.
      * simpl in H.
        assert (G: a' = iv \/ (exists i' : nat, nth_error l i' = Some iv)). {
          eapply IHl.
          apply H.
        }
        destruct G as [Gl | [gi Gr]].
        -- left. assumption.
        -- right. exists (S gi). simpl. assumption.
Qed.

Lemma less_than_all_sorted': forall x y l,
  x < y -> sorted' (y :: l) -> 
  forall i iv, nth_error (y :: l) i = Some iv -> x < iv.
Proof.
  intros x y l Hxy Hsorted.
  unfold sorted' in Hsorted.
  intro i.
  induction i.
  - simpl. intros iv H'. injection H' as H'.
    subst. assumption.
  - simpl. intros iv H'.
    assert (y <= iv). {
      apply (Hsorted 0 (S i) y iv).
      + lia.
      + reflexivity.
      + simpl. apply H'.
    }
    lia.
Qed.

Lemma remove_second_in_sorted: forall v v' l, sorted' (v :: v' :: l) -> sorted' (v :: l).
Proof.
  intros v v' l Hsorted i j vi vj Lij Hi Hj.
  destruct i; destruct j.
  - lia.
  - simpl in *.
    injection Hi as Hi; subst.
    apply (Hsorted 0 (S (S j)) vi vj).
    + lia.
    + reflexivity.
    + simpl. apply Hj.
  - lia.
  - simpl in *.
    apply (Hsorted (S (S i)) (S (S j)) vi vj).
    + lia.
    + simpl. apply Hi.
    + simpl. apply Hj.
Qed.

Lemma less_than_insert_to_tail: forall l v a,
  sorted' (v :: l) -> 
  a > v -> 
  forall i v', nth_error (insert a l) i = Some v' -> (v <= v').
Proof.
  intro l.
  induction l; simpl; intros v a' Hsorted La'v i v' H.
  - destruct i; simpl in H.
    + injection H as H; subst. lia.
    + destruct i; discriminate H.
  - bdestruct (a >=? a').
    + destruct i; simpl in H.
      * injection H as H; subst. lia.
      * apply (less_than_all_sorted v a l) with i.
        -- lia.
        -- apply sorted_tail with v. apply Hsorted.
        -- apply H.
    + destruct i; simpl in H.
      * injection H as H; subst.
        apply (Hsorted 0 1 v v').
        -- lia.
        -- reflexivity.
        -- reflexivity.
      * apply (IHl v a') with i.
        -- apply (remove_second_in_sorted _ _ _ Hsorted).
        -- assumption.
        -- apply H.
Qed.

Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros a l H.
  induction l.
  - simpl.
    unfold sorted'.
    intros i j iv jv Lij Hiv Hvj.
    destruct i; destruct j.
    + lia.
    + simpl in *. destruct j; discriminate Hvj.
    + lia.
    + simpl in *. destruct j; discriminate Hvj.
  - simpl.
    bdestruct (a0 >=? a).
    + unfold sorted'.
      intros i j iv jv Lij Hiv Hvj.
      destruct i; destruct j; try lia.
      * simpl in *.
        injection Hiv as Hiv; subst.
        apply (less_than_all_sorted iv a0 l H0 H j).
        assumption.
      * simpl in *.
        apply (H i j iv jv).
        -- lia.
        -- apply Hiv.
        -- apply Hvj.
    + intros i j iv jv Lij Hiv Hvj.
      destruct i; destruct j; try lia.
      * simpl in *.
        injection Hiv as Hiv; subst.
        apply (less_than_insert_to_tail _ _ _ H H0 j jv Hvj).
      * simpl in *.
        apply sorted_tail in H.
        apply IHl in H.
        apply (H i j iv jv).
        -- lia.
        -- apply Hiv.
        -- apply Hvj.
Qed.

Ltac inv H := inversion H; clear H; subst.

Theorem sort_sorted': forall l, sorted' (sort l).
Proof.
  induction l.
  - unfold sorted'. intros. destruct i; inv H0.
  - simpl. apply insert_sorted'. auto.
Qed.
