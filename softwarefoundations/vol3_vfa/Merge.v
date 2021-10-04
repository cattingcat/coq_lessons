From VFA Require Import Perm.
From VFA Require Import Sort.
From Coq Require Import Recdef. (* needed for Function feature *)

Fixpoint split {X:Type} (l:list X) : (list X * list X) :=
  match l with
  | []          => ([],[])
  | [x]         => ([x],[])
  | x1::x2::l'  =>
    let (l1,l2) := split l' in (x1::l1, x2::l2)
  end.

Definition list_ind2_principle:=
    forall (A : Type) (P : list A -> Prop),
      P [] ->
      (forall (a: A), P [a]) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall (l : list A), P l.

Fixpoint my_ind_foo (A : Type) (P : list A -> Prop) 
  (Pnil: P []) 
  (Pone: forall (a: A), P [a]) 
  (Ptwo: forall (a b : A) (l : list A), P l -> P (a :: b :: l))
  (l : list A) :=
    match l with 
    | nil => Pnil
    | [a] => Pone a
    | a :: b :: tail => Ptwo a b tail (my_ind_foo A P Pnil Pone Ptwo tail)
    end.

Definition list_ind2 :
  forall (A : Type) (P : list A -> Prop),
      P [] ->
      (forall (a: A), P [a]) ->
      (forall (a b: A) (l: list A), P l -> P (a :: b :: l)) ->
      forall (l : list A), P l :=
  fun (A : Type)
      (P : list A -> Prop)
      (H : P [])
      (H0 : forall (a: A), P [a])
      (H1 : forall (a b: A) (l: list A), P l -> P (a :: b :: l)) =>
    fix IH (l : list A) : P l :=
    match l with
    | []           => H
    | [x]          => H0 x
    | x :: y :: l' => H1 x y l' (IH l')
    end.

Lemma split_len': list_ind2_principle ->
    forall {X} (l:list X) (l1 l2: list X),
    split l = (l1,l2) ->
    length l1 <= length l /\
    length l2 <= length l.
Proof.
  unfold list_ind2_principle; intro IP.
  induction l using IP; intros.
  - inv H. lia.
  - inv H. simpl; lia.
  - inv H. destruct (split l) as [l1' l2']. inv H1.
    simpl.
    destruct (IHl l1' l2') as [P1 P2]; auto; lia.
Qed.

Lemma split_len: forall {X} (l: list X) (l1 l2: list X),
    split l = (l1,l2) ->
    length l1 <= length l /\
    length l2 <= length l.
Proof.
(*  apply (@split_len' my_ind_foo). *)
 apply (@split_len' list_ind2).
Qed.

Lemma split_perm : forall {X:Type} (l l1 l2: list X),
    split l = (l1,l2) -> Permutation l (l1 ++ l2).
Proof.
  induction l as [| x | x1 x2 l1' IHl'] using list_ind2; intros.
  - simpl in H. injection H as H1' H2'. subst. simpl.
    constructor.
  - simpl in H. injection H as H1' H2'. subst. simpl.
    constructor.
    constructor.
  - simpl in H.
    destruct (split l1') eqn:E.
    injection H as H1' H2'. subst. simpl.
    assert (G: Permutation l1' (l ++ l0)). { apply IHl'. reflexivity. }
    change (x1 :: l ++ x2 :: l0) with ([x1] ++ l ++ x2 :: l0).
    apply perm_trans with ([x1] ++ x2 :: l0 ++ l).
    + simpl.
      apply perm_skip.
      apply perm_skip.
      apply perm_trans with (l ++ l0).
        apply G.
        apply Permutation_app_comm.
    + apply Permutation_app_head.
      change (x2 :: l0 ++ l) with ((x2 :: l0) ++ l).
      apply (Permutation_app_comm).
Qed.

Fixpoint merge l1 l2 {struct l1} :=
  let fix merge_aux l2 :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | a1::l1', a2::l2' => if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
    end
  in merge_aux l2.

Print merge.

Lemma merge2 : forall (x1 x2:nat) r1 r2,
    x1 <= x2 ->
    merge (x1::r1) (x2::r2) = x1 :: merge r1 (x2::r2).
Proof.
  intros.
  simpl. (* This blows up in an unpleasant way, but we can
      still make some sense of it.  Look at the
      (fix merge_aux ...) term. It represents the
      the local function merge_aux after the value of the
      free variable l1 has been substituted by x1::r1,
      the match over l1 has been simplified to its
      second arm (the non-empty case) and x1 and r1 have
      been substituted for the pattern variables a1 and l1'. 
      The entire fix is applied to r2, but Coq won't attempt
      any further simplification until the structure of r2 
      is known. *)
  bdestruct (x1 <=? x2).
  - auto.
  - (* Since H and H0 are contradictory, this case follows by lia.
       But (ignoring that for the moment), note that we can get further 
       simplification to occur if we give some structure to l2: *)
    simpl. (* does nothing *)
    destruct r2; simpl. (* makes some progress *)
    + lia.
    + lia.
Qed.

Lemma merge_nil_l : forall l, merge [] l = l.
Proof.
  intros. simpl.
  (* Once again, we see a version of merge_aux specialized to
  the value l1 = nil. Now we see only the first arm (the
  empty case) of the match expression, which simply returns l2;
  in other words, here the fix is just the identity function. 
  And once again, the fix is applied to l.  Irritatingly,
  Coq _still_ refuses to perform the application unless l
  is destructured first (even though the answer is always l). *)
  destruct l.
  - auto.
  - auto.
Qed.

Function mergesort (l: list nat) {measure length l} : list nat :=
  match l with
  | []  => []
  | [x] => [x]
  | _   => let (l1,l2) := split l in
         merge (mergesort l1) (mergesort l2)
  end.
Proof.
  - (* recursive call on l1 *)
    intros.
    simpl in *. destruct (split l1) as [l1' l2'] eqn:E. inv teq1. simpl.
    destruct (split_len _ _ _ E).
    lia.
  - (* recursive call on l2 *)
    intros.
    simpl in *. destruct (split l1) as [l1' l2'] eqn:E. inv teq1. simpl.
    destruct (split_len _ _ _ E).
    lia.
Defined.

Check mergesort_equation. (* use it for undold *)
Check mergesort_ind.


Lemma sorted_merge1 : forall x x1 l1 x2 l2,
    x <= x1 -> x <= x2 ->
    sorted (merge (x1 :: l1) (x2 :: l2)) ->
    sorted (x :: merge (x1 :: l1) (x2 :: l2)).
Proof.
  intros x x1 l1 x2 l2 Hx1 Hx2 Hsorted.
  simpl in *.
  bdestruct (x2 >=? x1).
  - constructor. lia. apply Hsorted.
  - constructor. lia. apply Hsorted.
Qed.

Print sorted.
Lemma sorted_merge : forall l1, sorted l1 ->
                     forall l2, sorted l2 ->
                     sorted (merge l1 l2).
Proof.
  intros l1.
  induction l1.
  - intros _ l2 HSorted2. rewrite merge_nil_l. apply HSorted2.
  - intros HSorted1 l2.
    induction l2.
    + intros _.
      simpl. apply HSorted1.
    + intros HSorted2.
      simpl.
      bdestruct (a0 >=? a).
      * destruct l1 eqn:El1.
        ** simpl. constructor. apply H. apply HSorted2.
        ** apply sorted_merge1.
           inversion HSorted1; subst. lia. lia.
           apply IHl1. inversion HSorted1; subst. apply H4. apply HSorted2.
      * destruct l2 eqn:El2.
        ** constructor. lia. apply HSorted1.
        ** assert (G: sorted (a0 :: merge (a :: l1) (n :: l))). {
             apply sorted_merge1.
             - lia.
             - inversion HSorted2; subst. lia.
             - apply IHl2.
               inversion HSorted2; subst. apply H4.
           }
           apply G.
Qed.

Lemma mergesort_sorts: forall l, sorted (mergesort l).
Proof.
  apply mergesort_ind; intros.
  - constructor.
  - constructor.
  - apply sorted_merge.
    + apply H.
    + apply H0.
Qed.

Search Permutation.
Search (?l ++ []).

Lemma merge_perm: forall (l1 l2: list nat),
    Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  intros l1.
  induction l1.
  - intro l2. rewrite merge_nil_l with l2. simpl. apply Permutation_refl.
  - intro l2.
    induction l2.
    + rewrite app_nil_r. simpl. apply Permutation_refl.
    + simpl.
      bdestruct (a0 >=? a).
      * apply perm_skip.
        apply IHl1.
      * apply perm_trans with (a0 :: (a :: l1 ++ l2)).
        ** change (a :: l1 ++ a0 :: l2) with ((a :: l1) ++ [a0] ++ l2).
           apply perm_trans with ([a0] ++ (a :: l1) ++ l2).
            apply Permutation_app_swap_app.
            simpl. apply Permutation_refl.
        ** apply perm_skip.
           apply IHl2.
Qed.

Lemma mergesort_perm: forall l, Permutation l (mergesort l).
Proof.
  apply mergesort_ind; intros.
  - apply Permutation_refl.
  - apply Permutation_refl.
  - subst.
    apply perm_trans with ((mergesort l1) ++ (mergesort l2)).
    + apply split_perm in e0.
      apply perm_trans with (l1 ++ l2).
      * apply e0.
      * apply Permutation_app.
          apply H.
          apply H0.
    + apply merge_perm.
Qed.

Theorem mergesort_correct:
  is_a_sorting_algorithm mergesort.
Proof.
  split.
  apply mergesort_perm.
  apply mergesort_sorts.
Qed.
