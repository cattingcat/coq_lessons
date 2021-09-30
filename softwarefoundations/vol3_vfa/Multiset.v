Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Import FunctionalExtensionality.
From VFA Require Import Perm.
From VFA Require Import Sort.


Definition value := nat.
Definition multiset := value -> nat.

Definition empty : multiset := fun x => 0.

Definition singleton (v: value) : multiset :=
  fun x => if x =? v then 1 else 0.

Definition union (a b : multiset) : multiset :=
  fun x => a x + b x.



Lemma union_assoc: forall a b c : multiset,
   union a (union b c) = union (union a b) c.
Proof.
  intros.
  extensionality x.
  unfold union.
  lia.
Qed.

Lemma union_comm: forall a b : multiset,
   union a b = union b a.
Proof.
  intros.
  extensionality x.
  unfold union.
  lia.
Qed.

Lemma union_swap : forall a b c : multiset,
    union a (union b c) = union b (union a c).
Proof.
  intros.
  extensionality x.
  unfold union.
  lia.
Qed.


Fixpoint contents (al: list value) : multiset :=
  match al with
  | []      => empty
  | a :: bl => union (singleton a) (contents bl)
  end.

Example sort_pi_same_contents:
  contents (sort [3;1;4;1;5;9;2;6;5;3;5]) = contents [3;1;4;1;5;9;2;6;5;3;5].
Proof.
  extensionality x.
  repeat (destruct x; try reflexivity).
Qed.

Definition is_a_sorting_algorithm' (f: list nat -> list nat) := forall al,
    contents al = contents (f al) /\ sorted (f al).


Lemma insert_contents: forall x l,
     contents (insert x l) = contents (x :: l).
Proof.
  intros x l.
  induction l.
  - simpl. reflexivity.
  - extensionality o.
    unfold insert.
    bdestruct (a >=? x).
    + reflexivity.
    + fold insert.
      change (contents (x :: a :: l)) with (union (singleton x) (contents (a :: l))).
      change (contents (a :: insert x l)) with (union (singleton a) (contents (insert x l))).
      rewrite IHl.
      simpl.
      unfold union.
      lia.
Qed.

Theorem sort_contents: forall l,
    contents l = contents (sort l).
Proof.
  intro l.
  induction l.
  - reflexivity.
  - simpl.
    rewrite insert_contents.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Theorem insertion_sort_correct :
  is_a_sorting_algorithm' sort.
Proof.
  split.
  - apply sort_contents.
  - apply sort_sorted.
Qed.

Lemma perm_contents: forall (al bl : list nat),
    Permutation al bl -> contents al = contents bl.
Proof.
  intros al bl H.
  induction H.
  - reflexivity.
  - simpl. rewrite IHPermutation. reflexivity.
  - simpl. unfold union. extensionality o. lia.
  - rewrite IHPermutation1. apply IHPermutation2.
Qed.

Search (?a =? ?a).

Lemma contents_nil_inv : forall l, (forall x, 0 = contents l x) -> l = nil.
Proof.
  intros l H.
  induction l.
  - reflexivity.
  - exfalso.
    assert (G: 0 = contents (a :: l) a). {
      apply (H a).
    }
    simpl in G.
    unfold union in G.
    assert (G1: singleton a a = 1). {
      unfold singleton.
      rewrite Nat.eqb_refl.
      reflexivity.
    }
    rewrite G1 in G.
    discriminate G.
Qed.

Lemma contents_cons_inv : forall l x n,
    S n = contents l x ->
    exists l1 l2,
      l = l1 ++ x :: l2 /\ contents (l1 ++ l2) x = n.
Proof.
  intros l.
  induction l; simpl; intros x n H.
  - discriminate H.
  - unfold union, singleton in H.
    bdestruct (x =? a).
    + subst.
      exists nil, l.
      split.
      * simpl. reflexivity.
      * simpl. lia.
    + simpl in H.
      apply IHl in H.
      destruct H as [l1 [l2 [Hl Hr]]].
      exists (a :: l1), l2.
      split.
      * simpl. rewrite <- Hl. reflexivity.
      * simpl. unfold union. rewrite Hr.
        assert (G: singleton a x = 0). {
          unfold singleton.
          bdestruct (x =? a).
          - exfalso. apply (H0 H).
          - reflexivity.
        }
        rewrite G.
        reflexivity.
Qed.

Lemma contents_distr: forall l1 l2, 
  contents (l1 ++ l2) = union (contents (l1)) (contents (l2)).
Proof.
  intros l1.
  induction l1; simpl; intros l2.
  - unfold union.
    extensionality o.
    reflexivity.
  - rewrite -> IHl1.
    unfold union.
    extensionality o.
    lia.
Qed.


Lemma contents_insert_other : forall l1 l2 x y,
    y <> x -> contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y.
Proof.
  intros l1 l2 x.
  change ((l1 ++ x :: l2)) with ((l1 ++ [x] ++ l2)).
  intros y Hneq.
  repeat (rewrite contents_distr).
  unfold union.
  assert (contents [x] y = 0). {
    unfold contents, union, singleton.
    bdestruct (y =? x).
    - exfalso. apply (Hneq H).
    - reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Search (Permutation (?a ++ ?b) (?b ++ ?a)).

Lemma contents_perm: forall al bl,
    contents al = contents bl -> Permutation al bl.
Proof.
  intros al bl H0.
  assert (H: forall x, contents al x = contents bl x).
  { rewrite H0. auto. }
  clear H0.
  generalize dependent bl.
  induction al; intros bl H.
  - destruct bl.
    + constructor.
    + exfalso.
      assert (G: contents [] v = contents (v :: bl) v). { apply (H v). }
      unfold contents, union, singleton, empty in G.
      rewrite Nat.eqb_refl in G.
      simpl in G.
      discriminate G.
  - assert (G: contents (a :: al) a = contents bl a). { apply (H a). }
    assert (G1: contents (a :: al) a = S (contents al a)). {
      unfold contents, union, singleton.
      rewrite Nat.eqb_refl.
      simpl.
      reflexivity.
    }
    rewrite G1 in G.
    apply contents_cons_inv in G.
    destruct G as [l1 [l2 [Ebl Ecal]]].
    rewrite Ebl in H.
    assert (K: forall x : value, contents al x = contents (l1 ++ l2) x). {
      change (a :: al) with ([a] ++ al) in H.
      repeat (rewrite contents_distr in H).
      intros x.
      specialize (H x).
      simpl in H.
      unfold union in H.
      rewrite contents_distr.
      unfold union.
      unfold singleton, empty in H.
      bdestruct (x =? a).
      - simpl in H. lia.
      - simpl in H. lia.
    }
    assert (Permutation al (l1 ++ l2)). {
      apply IHal.
      apply K.
    }
    rewrite Ebl.
    Print Permutation.
    apply perm_trans with ((a :: l2) ++ l1).
    * simpl. apply perm_skip.
      apply perm_trans with (l1 ++ l2).
        assumption.
        apply Permutation_app_comm.
    * apply Permutation_app_comm.
Qed.



Theorem same_contents_iff_perm: forall al bl,
    contents al = contents bl <-> Permutation al bl.
Proof.
  intros al bl. split.
  - apply contents_perm.
  - apply perm_contents.
Qed.

Theorem sort_specifications_equivalent: forall sort,
    is_a_sorting_algorithm sort <-> is_a_sorting_algorithm' sort.
Proof.
  intros s. unfold is_a_sorting_algorithm, is_a_sorting_algorithm'. split.
  - intros H al.
    destruct (H al).
    split.
    + rewrite same_contents_iff_perm. assumption.
    + assumption.
  - intros H al.
    destruct (H al).
    split.
    + rewrite <- same_contents_iff_perm. assumption.
    + assumption.
Qed.
