Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.
Hint Constructors Permutation : core.
From Coq Require Export Lists.List.

Fixpoint select (x: nat) (l: list nat) : (nat * list nat) :=
  match l with
  | []      => (x, [])
  | h :: t  =>
    if x <=? h
    then let (j, l') := select x t in (j, h :: l')
    else let (j, l') := select h t in (j, x :: l')
  end.

Fail Fixpoint selsort (l : list nat) : list nat :=
  match l with
  | []      => []
  | x :: r  => let (y, r') := select x r in y :: selsort r'
  end.

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _     , O     => [] (* ran out of fuel *)
  | []    , _     => []
  | x :: r, S n'  => let (y, r') := select x r in y :: selsort r' n'
end.

Definition selection_sort (l : list nat) : list nat := selsort l (length l).


Example sort_pi :
  selection_sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  unfold selection_sort.
  simpl. reflexivity.
Qed.



Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted [i]
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).
Hint Constructors sorted : core.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).


Example pairs_example : forall (a c x : nat) (b d l : list nat),
    (a, b) = (let (c, d) := select x l in (c, d)) ->
    (a, b) = select x l.
Proof.
  intros. destruct (select x l) eqn:E. auto.
Qed.

Ltac gen x := generalize dependent x.

Lemma select_perm: forall x l y r,
    (y, r) = select x l -> Permutation (x :: l) (y :: r).
Proof.
  intros x l. gen x.
  induction l; simpl; intros x y r H.
  - injection H as Hl Hr; subst.
    constructor.
    constructor.
  - bdestruct (a >=? x).
    + destruct (select x l) eqn:E.
      injection H as Hl Hr; subst.
      change (x :: a :: l) with ([x] ++ [a] ++ l).
      change (n :: a :: l0) with ([n] ++ [a] ++ l0).
      apply perm_trans with ([a] ++ [x] ++ l).
      * apply Permutation_app_swap_app.
      * apply perm_trans with ([a] ++ [n] ++ l0).
        ** simpl. 
           apply perm_skip.
           apply IHl.
           symmetry.
           assumption.
        ** apply Permutation_app_swap_app.
    + destruct (select a l) eqn:E.
      injection H as Hl Hr; subst.
      change (n :: x :: l0) with ([n] ++ [x] ++ l0).
      apply perm_trans with ([x] ++ [n] ++ l0).
      * simpl.
        apply perm_skip.
        apply IHl.
        symmetry.
        assumption.
      * apply Permutation_app_swap_app.
Qed.

Lemma selsort_perm: forall n l,
    length l = n -> Permutation l (selsort l n).
Proof.
  intros n.
  induction n; intros l Hlen; simpl in Hlen.
  - simpl. destruct l. 
      constructor. 
      simpl in Hlen. discriminate.
  - unfold selsort.
    fold selsort.
    destruct l.
    + constructor.
    + destruct (select n0 l) eqn:E.
      symmetry in E.
      apply select_perm in E.
      apply perm_trans with (n1 :: l0).
      * assumption.
      * apply perm_skip.
        apply IHn.
        simpl in Hlen.
        Search Permutation.
        apply Permutation_length in E.
        simpl in E.
        lia.
Qed.

Lemma selection_sort_perm: forall l,
    Permutation l (selection_sort l).
Proof.
  intro l.
  unfold selection_sort.
  apply selsort_perm.
  reflexivity.
Qed.

Lemma select_rest_length : forall x l y r,
    select x l = (y, r) -> length l = length r.
Proof.
  intros.
  symmetry in H.
  apply select_perm in H.
  apply Permutation_length in H.
  simpl in H.
  lia.
Qed.


Lemma select_fst_leq: forall al bl x y,
    select x al = (y, bl) ->  y <= x.
Proof.
  intro al.
  induction al; simpl; intros bl x y Hsel.
  - injection Hsel as Exy.
    lia.
  - bdestruct (a >=? x).
    + destruct (select x al) eqn:E.
      injection Hsel as Hs1 Hs2.
      subst.
      apply IHal with l.
      assumption.
    + destruct (select a al) eqn:E.
      injection Hsel as Hs1 Hs2.
      subst.
      assert (G: y <= a). {
        apply IHal with l.
        assumption.
      }
      lia.
Qed.

Definition le_all x xs := Forall (fun y => x <= y) xs.

Infix "<=*" := le_all (at level 70, no associativity).

Lemma select_smallest: forall al bl x y,
    select x al = (y, bl) ->
    y <=* bl.
Proof.
  intro al.
  induction al; simpl; intros bl x y H.
  - injection H as Hl Hr.
    subst.
    unfold le_all.
    Search Forall.
    apply Forall_nil.
  - bdestruct (a >=? x).
    + destruct (select x al) eqn:E.
      injection H as Hl Hr.
      subst.
      assert (G1: y <=* l). {
        apply IHal with x.
        assumption.
      }
      assert (G2: y <= a). {
        apply select_fst_leq in E.
        lia.
      }
      apply Forall_cons.
      apply G2.
      apply G1.
    + destruct (select a al) eqn:E.
      injection H as Hl Hr.
      subst.
      assert (G1: y <=* l). {
        apply IHal with a.
        assumption.
      }
      assert (G2: y <= x). {
        apply select_fst_leq in E.
        lia.
      }
      apply Forall_cons.
      apply G2.
      apply G1.
Qed.

Lemma select_in : forall al bl x y,
    select x al = (y, bl) ->
    In y (x :: al).
Proof.
  intro al.
  induction al; simpl; intros bl x y H.
  - injection H as Hl Hr. left. assumption.
  - bdestruct (a >=? x).
    + destruct (select x al) eqn:E.
      injection H as Hl Hr.
      subst.
      apply IHal in E.
      destruct E.
      * left. assumption.
      * right. right. assumption.
    + destruct (select a al) eqn:E.
      injection H as Hl Hr.
      subst.
      apply IHal in E.
      destruct E.
      * right. left. assumption.
      * right. right. assumption.
Qed.


Lemma tst: forall l x y, x <=* l -> In y l -> x <= y.
Proof.
  intros l x y H1 H2.
  induction H1.
  - exfalso. apply H2.
  - destruct H2.
    + lia.
    + apply IHForall. apply H0.
Qed.

Lemma cons_of_small_maintains_sort: forall bl y n,
    n = length bl ->
    y <=* bl ->
    sorted (selsort bl n) ->
    sorted (y :: selsort bl n).
Proof.
  intros bl y n. gen bl. gen y.
  induction n; simpl; intros y bl Hn Hle Hsort.
  - destruct bl.
    + constructor.
    + simpl in Hn. discriminate Hn.
  - destruct bl as [| bh bt ].
    + simpl in Hn. discriminate Hn.
    + destruct (select bh bt) eqn:E.
      constructor.
      * apply select_in in E.
        apply tst with  (bh :: bt).
          assumption.
          assumption.
      * apply Hsort.
Qed.

Lemma selsort_sorted : forall n al,
    length al = n -> sorted (selsort al n).
Proof.
  intro n.
  induction n; simpl in *; intros al Hlen.
  - destruct al.
    + constructor.
    + discriminate Hlen.
  - destruct al.
    + discriminate Hlen.
    + destruct (select n0 al) eqn:E.
      Print sorted.
      apply cons_of_small_maintains_sort.
      * simpl in Hlen. apply select_rest_length in E. lia.
      * apply select_smallest in E. assumption.
      * apply IHn. apply select_rest_length in E. simpl in Hlen. lia.
Qed.

Lemma selection_sort_sorted : forall al,
    sorted (selection_sort al).
Proof.
  unfold selection_sort.
  intros al.
  apply selsort_sorted.
  reflexivity.
Qed.

Theorem selection_sort_is_correct :
  is_a_sorting_algorithm selection_sort.
Proof.
  intro a.
  split.
  - apply selection_sort_perm.
  - apply selection_sort_sorted.
Qed.



From VFA Require Import Multiset.
From Coq Require Import FunctionalExtensionality.

Module MultiserProof.

Definition is_a_sorting_algorithm' (f: list nat -> list nat) := forall al,
    contents al = contents (f al) /\ sorted (f al).

Lemma contents_cons: forall x l r, 
  contents l = contents r -> contents (x :: l) = contents (x :: r).
Proof.
  intros x l.
  induction l; intros r H.
  - simpl in H.
    simpl.
    rewrite <- H.
    reflexivity.
  - simpl in *.
    rewrite H.
    reflexivity.
Qed.

Lemma select_rest_multiset : forall x l y r,
    select x l = (y, r) -> contents (x :: l) = contents (y :: r).
Proof.
  intros x l. gen x.
  induction l; intros x y r H.
  - extensionality o.
    simpl in H.
    injection H as Hl Hr. subst.
    reflexivity.
  - extensionality o.
    simpl in H.
    bdestruct (a >=? x).
    + destruct (select x l) eqn:E.
      injection H as Hl Hr. subst.
      simpl.
      rewrite (union_swap (singleton x) (singleton a)).
      rewrite (union_swap (singleton y) (singleton a)).
      simpl in IHl.
      rewrite (IHl _ y l0).
        reflexivity.
        assumption.
    + destruct (select a l) eqn:E.
      injection H as Hl Hr. subst.
      simpl. simpl in IHl.
      rewrite (union_swap (singleton y) (singleton x)).
      rewrite <- (IHl a y l0).
        reflexivity.
        assumption.
Qed.

Lemma same_contents_same_len: forall l1 l2, 
  contents l1 = contents l2 -> length l1 = length l2.
Proof.
  intro l1.
  induction l1; intros l2 H.
  - simpl in H.
    destruct l2.
    + reflexivity.
    + exfalso.
      apply equal_f with v in H.
      simpl in H.
      unfold union, singleton, empty in H.
      rewrite Nat.eqb_refl in H.
      discriminate H.
  - assert (G: S (contents l1 a) = contents l2 a). {
      apply equal_f with a in H.
      simpl in H.
      unfold union, singleton, empty in H.
      rewrite Nat.eqb_refl in H.
      simpl in H.
      assumption.
    }
    destruct (contents_cons_inv _ _ _ G) as [l1' [l2' [Hl Hcont]]].
    rewrite Hl.
    rewrite app_length. simpl.
    rewrite Nat.add_comm. simpl.
    rewrite <- app_length.
    rewrite <- (IHl1 (l2' ++ l1')).
    + reflexivity.
    + extensionality o.
      rewrite Hl in H.
      rewrite contents_distr in *.
      simpl in H.
      apply equal_f with o in H.
      unfold union, singleton, empty in *.
      bdestruct (o =? a).
      * lia.
      * lia.
Qed.

Lemma selsort_multiset: forall n l,
    length l = n -> contents l = contents (selsort l n).
Proof.
  intros n.
  induction n; intros l Hlen; simpl in Hlen.
  - extensionality o.
    simpl. destruct l. 
      constructor. 
      simpl in Hlen. discriminate.
  - unfold selsort.
    fold selsort.
    destruct l.
    + constructor.
    + destruct (select v l) eqn:E.
      apply select_rest_multiset in E.
      extensionality o.
      assert (E' := E).
      eapply equal_f in E.
      rewrite E.
      simpl.
      rewrite <- IHn.
      * reflexivity.
      * simpl in Hlen.
        assert (G: length l0 = length l). {
          apply same_contents_same_len in E'.
          simpl in E'.
          injection E' as E'.
          rewrite E'.
          reflexivity.
        }
        rewrite <- G in Hlen.
        injection Hlen as Hlen.
        apply Hlen.
Qed.

Lemma selection_sort_multiset : forall al,
    contents al = contents (selection_sort al).
Proof.
  intro al.
  apply selsort_multiset.
  reflexivity.
Qed.

Theorem selection_sort_is_correct' :
  is_a_sorting_algorithm' selection_sort.
Proof.
  intro a.
  split.
  - apply selection_sort_multiset.
  - apply selection_sort_sorted.
Qed.

End MultiserProof.



Require Import Recdef.

Function selsort' l {measure length l} :=
  match l with
  | []      => []
  | x :: r  => let (y, r') := select x r
               in y :: selsort' r'
end.

Proof.
  intros.
  assert (Hperm: Permutation (x :: r) (y :: r')).
  { apply select_perm. auto. }
  apply Permutation_length in Hperm.
  inv Hperm. simpl. lia.
Defined.

Print selsort'.
Print selsort'_terminate.
Check selsort'_equation.


Lemma selsort'_perm : forall n l,
    length l = n -> Permutation l (selsort' l).
Proof.
(* TODO *)
Admitted.
