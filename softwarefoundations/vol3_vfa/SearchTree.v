Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From VFA Require Import Perm.
From VFA Require Import Maps.
From VFA Require Import Sort.

Definition key := nat.

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).
Arguments E {V}.
Arguments T {V}.

Definition empty_tree {V : Type} : tree V := E.

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E         => false
  | T l y v r => if x <? y 
                  then bound x l
                  else (if x >? y then bound x r else true)
  end.

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E         => d
  | T l y v r => if x <? y 
                  then lookup d x l
                  else (if x >? y then lookup d x r else v)
  end.


Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E           => T E x v E
  | T l y v' r => if x <? y 
                  then T (insert x v l) y v' r
                  else (if x >? y then T l y v' (insert x v r) else T l x v r)
  end.

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E         => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).
Hint Constructors BST: core.

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
  intros. constructor. Qed.

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> 
    forall (k : key) (v : V), P k v -> ForallT P (insert k v t).
Proof.
  intros V P t.
  induction t; intros H k' v' Pkv.
  - simpl. auto.
  - simpl in *.
    destruct H as [H1 [H2 H3]].
    bdestruct (k >? k').
    + simpl. repeat split.
      * assumption.
      * apply (IHt1 H2 k' v' Pkv).
      * assumption.
    + bdestruct (k' >? k).
      ++ simpl. repeat split.
         * assumption.
         * assumption.
         * apply (IHt2 H3 k' v' Pkv).
      ++ simpl. repeat split.
         * assumption.
         * assumption.
         * assumption.
Qed.


Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
  intros V k v t.
  induction t; intros H.
  - simpl. apply BST_T.
    + simpl. constructor.
    + simpl. constructor.
    + constructor.
    + constructor.
  - inversion H; subst.
    simpl in *.
    bdestruct (k0 >? k).
    + apply BST_T.
      * apply ForallT_insert.
          apply H4.
          apply H0.
      * apply H5.
      * apply IHt1.
        apply H6.
      * apply H7.
    + bdestruct (k >? k0); simpl.
      ++ apply BST_T.
         * apply H4.
         * apply ForallT_insert.
             apply H5.
             lia.
         * apply H6.
         * apply IHt2.
           apply H7.
      ++ assert (G: k = k0). { lia. }
         apply BST_T; auto.
         * rewrite G.
           apply H4.
         * rewrite G.
           apply H5.
Qed.


Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; simpl.
  - bdestruct (k <? k); try lia; auto.
  - bdestruct (k <? k0); bdestruct (k0 <? k); simpl; try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k0 <? k0); try lia; auto.
Qed.


Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =?  ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <?  ?Y then _ else _ ] => bdestruct (X <? Y)
  end.

Ltac bdall := repeat (simpl; bdestruct_guard; try lia; auto).

Theorem lookup_insert_eq' :  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

Theorem lookup_insert_neq : forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
  induction t; intros; bdall.
Qed.

Theorem bound_insert_eq' :  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    bound k (insert k v t) = true.
Proof.
  induction t; intros; bdall.
Qed.

Theorem bound_insert_neq : forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> bound k' (insert k v t) = bound k' t.
Proof.
  induction t; intros; bdall.
Qed.

Theorem bound_empty : forall (V : Type) (k : key),
    @bound V k empty_tree = false.
Proof.
  auto.
Qed.

Theorem bound_default :  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false ->
    lookup d k t = d.
Proof.
  induction t; intros.
  - simpl in *. reflexivity.
  - simpl in *.
    bdall.
Qed.

Lemma lookup_insert_shadow :forall (V : Type) (t : tree V) (v v' d: V) (k k' : key),
    lookup d k' (insert k v (insert k v' t)) = lookup d k' (insert k v t).
Proof.
  intros. bdestruct (k =? k').
  - subst.
    rewrite lookup_insert_eq'.
    rewrite lookup_insert_eq'.
    reflexivity.
  - rewrite lookup_insert_neq; try assumption.
    rewrite lookup_insert_neq; try assumption.
    rewrite lookup_insert_neq; try assumption.
    reflexivity.
Qed.

Lemma lookup_insert_same :forall (V : Type) (k k' : key) (d : V) (t : tree V),
    lookup d k' (insert k (lookup d k t) t) = lookup d k' t.
Proof.
  intros. bdestruct (k =? k').
  - subst.
    rewrite lookup_insert_eq'.
    reflexivity.
  - rewrite lookup_insert_neq; try assumption.
    reflexivity.
Qed.

Lemma lookup_insert_permute :forall (V : Type) (v1 v2 d : V) (k1 k2 k': key) (t : tree V),
    k1 <> k2 ->
    lookup d k' (insert k1 v1 (insert k2 v2 t))
        = lookup d k' (insert k2 v2 (insert k1 v1 t)).
Proof.
  intros. bdestruct (k' =? k1).
  - subst.
    rewrite lookup_insert_eq'.
    rewrite lookup_insert_neq; try auto.
    rewrite lookup_insert_eq'.
    reflexivity.
  - rewrite lookup_insert_neq; try auto.
    bdestruct (k' =? k2).
    + subst.
      rewrite lookup_insert_eq'.
      rewrite lookup_insert_eq'.
      reflexivity.
    + rewrite lookup_insert_neq; try auto.
      rewrite lookup_insert_neq; try auto.
      rewrite lookup_insert_neq; try auto.
Qed.

Lemma insert_shadow_equality : forall (V : Type) (t : tree V) (k : key) (v v' : V),
    insert k v (insert k v' t) = insert k v t.
Proof.
  induction t; intros; bdall.
  - rewrite IHt1; auto.
  - rewrite IHt2; auto.
Qed.


Lemma insert_same_equality_breaks :
  exists (V : Type) (d : V) (t : tree V) (k : key),
      insert k (lookup d k t) t <> t.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma insert_permute_equality_breaks :
  exists (V : Type) (v1 v2 : V) (k1 k2 : key) (t : tree V),
    k1 <> k2 /\ insert k1 v1 (insert k2 v2 t) <> insert k2 v2 (insert k1 v1 t).
Proof.
  exists nat, 2, 3, 2, 3, (insert 1 1 empty_tree).
  simpl. split.
  - auto.
  - intros H.
    injection H as H1 H2.
    discriminate H1.
Qed.


Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E         => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.


Definition elements_complete_spec :=  forall (V : Type) (k : key) (v d : V) (t : tree V),
    bound k t = true ->
    lookup d k t = v ->
    In (k, v) (elements t).

Theorem elements_complete : elements_complete_spec.
Proof.
  unfold elements_complete_spec.
  induction t; simpl; intros.
  - discriminate H.
  - bdestruct (k0 >? k).
    + apply in_or_app.
      left.
      apply IHt1; assumption.
    + bdestruct (k >? k0).
      * apply in_or_app.
        right. simpl. right.
        apply IHt2; assumption.
      * assert (G: k = k0). { lia. }
        subst.
        apply in_or_app.
        right. simpl. left.
        reflexivity.
Qed.


Definition elements_correct_spec := forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements t) ->
    bound k t = true /\ lookup d k t = v.


Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.
Hint Transparent uncurry: core.

Lemma elements_preserves_forall : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    Forall (uncurry P) (elements t).
Proof.
  intros V P t.
  induction t; simpl; intros.
  - constructor.
  - destruct H as [H1 [H2 H3]].
    apply IHt1 in H2.
    apply IHt2 in H3.
    apply Forall_app.
    split; try assumption.
    constructor; try assumption.
Qed.

Lemma elements_preserves_relation : forall (V : Type) (k k' : key) (v : V) (t : tree V) (R : key -> key -> Prop),
    ForallT (fun y _ => R y k') t ->
    In (k, v) (elements t) ->
    R k k'.
Proof.
  intros V k k' v t.
  induction t; simpl; intros.
  - exfalso. apply H0.
  - destruct H as [H1 [H2 H3]].
    Search In.
    apply in_app_or in H0. simpl in H0.
    destruct H0 as [H0 | [H0 | H0]].
    + apply IHt1.
      apply H2.
      apply H0.
    + injection H0 as H01 H02; subst.
      apply H1.
    + apply IHt2.
      apply H3.
      apply H0.
Qed.

Theorem elements_correct : elements_correct_spec.
Proof.
  unfold elements_correct_spec.
  induction t; simpl; intros.
  - exfalso. apply H0.
  - inversion H; subst.
    apply in_app_or in H0. simpl in H0.
    destruct H0 as [H0 | [H0 | H0]].
    + assert (G: k < k0). { eapply elements_preserves_relation. apply H5. apply H0. }
      assert (G': k0 >? k = true). { bdestruct (k0 >? k); lia. }
      rewrite G'; simpl.
      apply IHt1.
        assumption.
        assumption.
    + injection H0 as H01 H02; subst.
      assert (k >? k = false). { bdestruct (k >? k); lia. }
      rewrite H0.
      auto.
    + assert (G: k > k0). { eapply elements_preserves_relation. apply H6. apply H0. }
      assert (G': k0 <? k = true). { bdestruct (k0 <? k); lia. }
      assert (G'': k0 >? k = false). { bdestruct (k0 >? k); lia. }
      rewrite G'; simpl.
      rewrite G''; simpl.
      apply IHt2.
        assumption.
        assumption.
Qed.

Theorem elements_complete_inverse :forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t ->
    bound k t = false ->
    ~(In (k, v) (elements t)).
Proof.
  unfold not.
  intros.
  destruct (elements_correct V k v v t H H1).
  rewrite H2 in H0.
  discriminate H0.
Qed.

Lemma bound_value : forall (V : Type) (k : key) (t : tree V),
    bound k t = true -> exists v, forall d, lookup d k t = v.
Proof.
  induction t; simpl; intros.
  - exfalso. discriminate H.
  - bdestruct (k0 >? k).
    + apply IHt1.
      assumption.
    + bdestruct (k >? k0).
      * apply IHt2.
        assumption.
      * exists v.
        intro V'.
        reflexivity.
Qed.

Theorem elements_correct_inverse :  forall (V : Type) (k : key) (t : tree V),
    (forall v, ~ In (k, v) (elements t)) ->
    bound k t = false.
Proof.
  intros.
  destruct (bound k t) eqn:E.
  - destruct (bound_value _ _ _ E) as [v Hl].
    exfalso. apply (H v).
    apply (elements_complete V k v v).
      apply E.
      apply Hl.
  - reflexivity.
Qed.

(* Part 2: Sorted (Advanced) *)


Lemma sorted_app: forall l1 l2 x,
  Sort.sorted l1 -> Sort.sorted l2 ->
  Forall (fun n => n < x) l1 -> Forall (fun n => n > x) l2 ->
  Sort.sorted (l1 ++ x :: l2).
Proof.
  intro l1.
  induction l1; simpl; intros.
  - destruct l2.
    + constructor.
    + inversion H2; subst.
      constructor; try lia; try assumption.
  - inversion H1; subst.
    inversion H; subst.
    + simpl.
      constructor.
      * lia.
      * simpl in IHl1.
        apply IHl1; auto.
        constructor.
    + simpl.
      constructor.
      * apply H7.
      * simpl in IHl1.
        apply IHl1; auto.
Qed.

Definition list_keys {V : Type} (lst : list (key * V)) :=  map fst lst.

Search (map ?f (?l1 ++ ?l2)).
Search (Forall ?p (?l1 ++ ?l2)).

Lemma forall_transform: forall V P t,
  ForallT (fun (k : key) (_ : V) => P k) t -> Forall (fun k : key => P k) (map fst (elements t)).
Proof.
  intros V P t.
  induction t; simpl; intros.
  - constructor.
  - destruct H as [H1 [H2 H3]].
    apply IHt1 in H2.
    apply IHt2 in H3.
    rewrite map_app.
    apply Forall_app.
    split.
    + apply H2.
    + simpl.
      constructor.
      * apply H1.
      * apply H3.
Qed.

Theorem sorted_elements : forall (V : Type) (t : tree V),
    BST t -> Sort.sorted (list_keys (elements t)).
Proof.
  intros V t.
  induction t; simpl; intros.
  - constructor.
  - unfold list_keys in *.
    rewrite map_app.
    simpl.
    inversion H; subst.
    apply sorted_app; auto.
    + apply forall_transform.
      apply H4.
    + apply forall_transform.
      apply H5.
Qed.


(* Part 3: No Duplicates *)
Print NoDup.

Definition disjoint {X:Type} (l1 l2: list X) := forall (x : X),
    In x l1 -> ~In x l2.

Search (In ?a (?l1 ++ ?l2)).
Lemma NoDup_append : forall (X:Type) (l1 l2: list X),
  NoDup l1 -> 
  NoDup l2 -> 
  disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  intros X l1.
  induction l1; simpl; intros.
  - apply H0.
  - inversion H; subst.
    constructor.
    + assert (G: ~ In a l2). {
        specialize (H1 a).
        simpl in H1.
        apply H1.
        left.
        reflexivity.
      }
      intros HContra.
      apply in_app_or in HContra.
      destruct HContra.
      * apply H4. apply H2.
      * apply G. apply H2.
    + apply IHl1; auto.
      intros x HIn HContra.
      apply (H1 x).
      * simpl. right. apply HIn.
      * apply HContra.
Qed.

Search Forall.

Theorem elements_nodup_keys : forall (V : Type) (t : tree V),
    BST t ->
    NoDup (list_keys (elements t)).
Proof.
  intros.
  induction H; simpl.
  - constructor.
  - unfold list_keys in *.
    rewrite map_app.
    simpl.
    apply NoDup_append.
    + assumption.
    + constructor.
      * apply forall_transform in H, H0.
        rewrite Forall_forall in H, H0.
        intro HContra.
        apply H0 in HContra.
        lia.
      * assumption.
    + intros x' Hl Hr.
      simpl in Hr.
      apply forall_transform in H, H0.
      rewrite Forall_forall in H, H0.
      assert (G: x' < x). { apply H. apply Hl. }
      destruct Hr as [Hr | Hr].
      * lia.
      * assert (G': x' > x). { apply H0. apply Hr. }
        lia.
Qed.




Fixpoint fast_elements_tr {V : Type} (t : tree V)
         (acc : list (key * V)) : list (key * V) :=
  match t with
  | E         => acc
  | T l k v r => fast_elements_tr l ((k, v) :: fast_elements_tr r acc)
  end.

Definition fast_elements {V : Type} (t : tree V) : list (key * V) :=
  fast_elements_tr t [].

Lemma fast_elements_tr_helper : forall (V : Type) (t : tree V) (lst : list (key * V)),
    fast_elements_tr t lst = elements t ++ lst.
Proof.
  intros V t.
  induction t; simpl; intros.
  - reflexivity.
  - rewrite IHt1.
    rewrite IHt2.
    rewrite app_assoc_reverse.
    reflexivity.
Qed.


Lemma fast_elements_eq_elements : forall (V : Type) (t : tree V),
    fast_elements t = elements t.
Proof.
  intros V t.
  induction t; simpl.
  - reflexivity.
  - unfold fast_elements. simpl.
    rewrite fast_elements_tr_helper.
    rewrite fast_elements_tr_helper.
    rewrite app_nil_r.
    reflexivity.
Qed.

Corollary fast_elements_correct : forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (fast_elements t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
  intros. rewrite fast_elements_eq_elements in *.
  apply elements_correct; assumption.
Qed.


(* An Algebraic Specification of elements *)

Fixpoint kvs_insert {V : Type} (k : key) (v : V) (kvs : list (key * V)) :=
  match kvs with
  | []               => [(k, v)]
  | (k', v') :: kvs' =>
    if k <? k' then (k, v) :: kvs
    else if k >? k' then (k', v') :: kvs_insert k v kvs'
         else (k, v) :: kvs'
  end.

Lemma kvs_insert_split :
  forall (V : Type) (v v0 : V) (e1 e2 : list (key * V)) (k k0 : key),
    Forall (fun '(k',_) => k' < k0) e1 ->
    Forall (fun '(k',_) => k' > k0) e2 ->
    kvs_insert k v (e1 ++ (k0,v0) :: e2) =
    if k <? k0 then
      (kvs_insert k v e1) ++ (k0,v0)::e2
    else if k >? k0 then
           e1 ++ (k0,v0)::(kvs_insert k v e2)
         else
           e1 ++ (k,v)::e2.
Proof. Admitted.

Lemma kvs_insert_elements : forall (V : Type) (t : tree V),
    BST t ->
    forall (k : key) (v : V), elements (insert k v t) = kvs_insert k v (elements t).
Proof. Admitted.


(* Model-based Specifications*)

Fixpoint map_of_list {V : Type} (el : list (key * V)) : partial_map V :=
  match el with
  | []            => empty
  | (k, v) :: el' => update (map_of_list el') k v
  end.

Definition Abs {V : Type} (t : tree V) : partial_map V :=  map_of_list (elements t).

Definition find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | Some v => v
  | None => d
  end.

Definition map_bound {V : Type} (k : key) (m : partial_map V) : bool :=
  match m k with
  | Some _ => true
  | None => false
  end.


Lemma in_fst : forall (X Y: Type) (lst: list (X * Y)) (x: X) (y: Y),
    In (x, y) lst -> In x (map fst lst).
Proof.
  intros X Y lst.
  induction lst; simpl; intros.
  - apply H.
  - destruct H.
    + left. rewrite H. reflexivity.
    + right. eapply IHlst. apply H.
Qed.

Lemma in_map_of_list : forall (V: Type) (el: list (key * V)) (k: key) (v: V),
    NoDup (map fst el) ->
    In (k,v) el -> 
    (map_of_list el) k = Some v.
Proof.
  intros V el.
  induction el; simpl; intros.
  - exfalso. apply H0.
  - destruct H0.
    + rewrite H0.
      unfold update, t_update.
      rewrite Nat.eqb_refl.
      reflexivity.
    + destruct a.
      unfold update, t_update.
      simpl in H.
      inversion H; subst.
      assert (G: k0 <> k). {
        intros HContra.
        subst.
        apply in_fst in H0.
        apply H3. apply H0.
      }
      rewrite <- Nat.eqb_neq in G.
      rewrite G.
      apply IHel.
      * inversion H; subst.
        assumption.
      * assumption.
Qed.



Lemma not_in_map_of_list : forall (V: Type) (el: list (key * V)) (k: key),
    ~In k (map fst el) -> (map_of_list el) k = None.
Proof.
  intros V el.
  induction el; simpl; intros.
  - reflexivity.
  - destruct a.
    unfold update, t_update.
    assert (G: k0 =? k = false). {
      apply Nat.eqb_neq.
      intro Hcontra.
      apply H. left. simpl. assumption.
    }
    rewrite G.
    apply IHel.
    assert (G' : ~ In k (map fst el)). {
      intro HContra.
      apply H. right. assumption.
    }
    apply G'.
Qed.

Lemma empty_relate : forall (V: Type),
    @Abs V empty_tree = empty.
Proof.
  reflexivity.
Qed.

Lemma elem_not_match_list: forall V P (t: list (key * V)) k',
  Forall (fun '(k, v) => P k) t ->
  ~P k' ->
  map_of_list t k' = None.
Proof.
  intros V P t.
  induction t; intros.
  - simpl. reflexivity.
  - simpl.
    destruct a.
    inversion H; subst.
    unfold update, t_update.
    bdestruct (k =? k').
    + subst. exfalso. apply H0. apply H3.
    + apply IHt.
      assumption.
      assumption.
Qed.

Lemma elim_not_suitable_app_l: forall V P (l r: list (key * V)) k',
  Forall (fun '(k, v) => P k) l ->
  ~P k' ->
  map_of_list (l ++ r) k' = map_of_list r k'.
Proof.
  intros V P l.
  induction l; simpl; intros.
  - reflexivity.
  - destruct a.
    unfold update, t_update.
    inversion H; subst.
    bdestruct (k =? k').
    + subst. exfalso. apply H0. apply H3.
    + apply IHl; auto.
Qed.

Lemma elim_not_suitable_app_r: forall V P (l r: list (key * V)) k',
  Forall (fun '(k, v) => P k) r ->
  ~P k' ->
  map_of_list (l ++ r) k' = map_of_list l k'.
Proof.
  intros V P l.
  induction l; simpl; intros.
  - unfold empty, t_empty. simpl.
    eapply elem_not_match_list.
      apply H.
      apply H0.
  - destruct a.
    unfold update, t_update.
    bdestruct (k =? k').
    + reflexivity.
    + apply IHl; auto.
Qed.


Lemma forall_trans_pm: forall V P (l: list (key * V)),
  Forall (fun k : key => P k) (map fst l) -> Forall (fun '(k, _) => P k) l.
Proof.
  intros.
  induction l.
  - auto.
  - inversion H; subst.
    constructor.
    + destruct a.
      simpl in H2.
      assumption.
    + auto.
Qed.


Theorem bound_relate : forall (V: Type) (t: tree V) (k: key),
    BST t ->
    map_bound k (Abs t) = bound k t.
Proof.
  intros V t.
  induction t; simpl; intros.
  - reflexivity.
  - unfold Abs. simpl.
    inversion H; subst.
    unfold map_bound.
    bdestruct (k >? k0).
    + rewrite elim_not_suitable_app_r with (P := fun x => x >= k).
      * apply IHt1. assumption.
      * constructor.
        ** lia.
        ** apply forall_transform in H5.
           apply forall_trans_pm.
           apply Forall_impl with (Q := fun x => x >= k)in H5.
           *** apply H5.
           *** intros. lia.
      * lia.
    + rewrite elim_not_suitable_app_l with (P := fun x => x < k).
      * bdestruct (k0 >? k).
        ** simpl. unfold update, t_update.
           bdestruct (k =? k0).
            *** exfalso. lia.
            *** apply IHt2. assumption.
        ** simpl. unfold update, t_update.
           bdestruct (k =? k0).
            *** reflexivity.
            *** exfalso. lia.
      * apply forall_transform in H4.
        apply forall_trans_pm.
        apply H4.
      * lia.
Qed.


Lemma lookup_relate : forall (V: Type) (t: tree V) (d: V) (k: key),
    BST t -> find d k (Abs t) = lookup d k t.
Proof.
  intros V t.
  induction t; simpl; intros.
  - reflexivity.
  - unfold Abs, find. simpl.
    inversion H; subst.
    bdestruct (k >? k0).
    + rewrite elim_not_suitable_app_r with (P := fun x => x >= k).
      * apply IHt1. assumption.
      * constructor.
        ** lia.
        ** apply forall_transform in H5.
           apply forall_trans_pm.
           apply Forall_impl with (Q := fun x => x >= k)in H5.
           *** apply H5.
           *** intros. lia.
      * lia.
    + rewrite elim_not_suitable_app_l with (P := fun x => x < k).
      * bdestruct (k0 >? k).
        ** simpl. unfold update, t_update.
           bdestruct (k =? k0).
            *** exfalso. lia.
            *** apply IHt2. assumption.
        ** simpl. unfold update, t_update.
           bdestruct (k =? k0).
            *** reflexivity.
            *** exfalso. lia.
      * apply forall_transform in H4.
        apply forall_trans_pm.
        apply H4.
      * lia.
Qed.

From Coq Require Import FunctionalExtensionality.

Lemma insert_relate : forall (V: Type) (t: tree V) (k: key) (v: V),
  BST t -> Abs (insert k v t) = update (Abs t) k v.
Proof.
  (* TODO: find a direct proof that doesn't rely on kvs_insert_elements *)
    unfold Abs.
  intros.
  rewrite kvs_insert_elements; auto.
  remember (elements t) as l.
  clear -l. (* clear everything not about l *)
  induction l.
  - reflexivity.
  - simpl.
    unfold update, t_update. simpl.
    destruct a.
    extensionality o.
    bdestruct (k0 >? k).
    + simpl. unfold update, t_update. simpl.
      reflexivity.
    + bdestruct (k >? k0).
      * simpl. unfold update, t_update in *. simpl.
        rewrite (IHl).
        bdestruct (k0 =? o); bdestruct (k =? o).
        ** exfalso. lia.
        ** reflexivity.
        ** reflexivity.
        ** reflexivity.
      * simpl. unfold update, t_update in *. simpl.
        bdestruct (k0 =? o); bdestruct (k =? o).
        ** reflexivity. 
        ** exfalso. lia.
        ** reflexivity.
        ** reflexivity.
Qed.

Lemma elements_relate : forall (V: Type) (t: tree V),
  BST t ->
  map_of_list (elements t) = Abs t.
Proof.
  unfold Abs. intros. reflexivity.
Qed.


(* An Alternative Abstraction Relation *)

Definition union {X} (m1 m2: partial_map X) : partial_map X :=
  fun k =>
    match (m1 k, m2 k) with
    | (None,   None)   => None
    | (None,   Some v) => Some v
    | (Some v, None)   => Some v
    | (Some _, Some _) => None
    end.

Lemma union_left : forall {X} (m1 m2: partial_map X) k,
    m2 k = None -> union m1 m2 k = m1 k.
Proof.
  intros.
  unfold union.
  rewrite H.
  destruct (m1 k); reflexivity.
Qed.

Lemma union_right : forall {X} (m1 m2: partial_map X) k,
    m1 k = None -> union m1 m2 k = m2 k.
Proof.
  intros.
  unfold union.
  rewrite H.
  destruct (m2 k); reflexivity.
Qed.

Lemma union_both : forall {X} (m1 m2 : partial_map X) k v1 v2,
    m1 k = Some v1 ->
    m2 k = Some v2 ->
    union m1 m2 k = None.
Proof.
  intros.
  unfold union.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma union_update_right : forall {X} (m1 m2: partial_map X) k v,
    m1 k = None ->
    update (union m1 m2) k v = union m1 (update m2 k v).
Proof.
  intros.
  unfold union, update, t_update.
  extensionality o.
  bdestruct (k =? o).
  - subst. rewrite H. reflexivity.
  - reflexivity.
Qed.

Lemma union_update_left : forall {X} (m1 m2: partial_map X) k v,
    m2 k = None ->
    update (union m1 m2) k v = union (update m1 k v) m2.
Proof.
  intros.
  unfold union, update, t_update.
  extensionality o.
  bdestruct (k =? o).
  - subst. rewrite H. reflexivity.
  - reflexivity.
Qed.

Fixpoint map_of_tree {V : Type} (t: tree V) : partial_map V :=
  match t with
  | E         => empty
  | T l k v r => update (union (map_of_tree l) (map_of_tree r)) k v
  end.

Lemma map_of_tree_prop : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    forall k v, (map_of_tree t) k = Some v -> P k v.
Proof.
  intros V P t.
  induction t; simpl; intros.
  - unfold empty, t_empty in H0. discriminate H0.
  - unfold update, t_update in H0.
    destruct H as [Pkv [Pt1 Pt2]].
    bdestruct (k =? k0).
    + injection H0 as H0. subst. apply Pkv.
    + unfold union, update, t_update in H0.
      destruct (map_of_tree t1 k0) eqn:E1; destruct (map_of_tree t2 k0) eqn:E2.
      * discriminate H0.
      * injection H0 as H0. subst.
        apply IHt1; assumption.
      * injection H0 as H0. subst.
        apply IHt2; assumption.
      * discriminate H0.
Qed.


Definition Abs' {V : Type} (t: tree V) : partial_map V :=
  map_of_tree t.

Lemma empty_relate' : forall (V : Type),
    @Abs' V empty_tree = empty.
Proof.
  reflexivity.
Qed.


Theorem bound_relate' : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs' t) = bound k t.
Proof.
  intros V t.
  induction t; simpl; intros.
  - reflexivity.
  - unfold map_bound.
    inversion H; subst.
    unfold Abs', update, t_update in *.
    bdestruct (k =? k0).
    + assert (G1: k >? k0 = false). { bdestruct(k >? k0); lia. }
      assert (G2: k0 >? k = false). { bdestruct(k0 >? k); lia. }
      rewrite G1, G2.
      reflexivity.
    + bdestruct (k >? k0); bdestruct (k0 >? k).
      * exfalso. lia.
      * unfold union.
        destruct (map_of_tree t2 k0) eqn:E.
        ** assert(G:= (map_of_tree_prop _ _ _ H5 _ _ E)).
           simpl in G.
           exfalso. lia.
        ** specialize (IHt1 k0 H6).
           unfold map_bound in IHt1.
           destruct (map_of_tree t1 k0) eqn:E'.
           *** assumption.
           *** assumption.
      * unfold union.
        destruct (map_of_tree t1 k0) eqn:E.
        ** assert(G:= (map_of_tree_prop _ _ _ H4 _ _ E)).
           simpl in G.
           exfalso. lia.
        ** specialize (IHt2 k0 H7).
           unfold map_bound in IHt2.
           destruct (map_of_tree t2 k0) eqn:E'.
           *** assumption.
           *** assumption.
      * exfalso. lia.
Qed.

Lemma lookup_relate' : forall (V : Type) (d : V) (t : tree V) (k : key),
    BST t -> find d k (Abs' t) = lookup d k t.
Proof.
  intros V d t.
  induction t; simpl; intros.
  - reflexivity.
  - unfold find.
    inversion H; subst.
    unfold Abs', update, t_update in *.
    bdestruct (k =? k0).
    + assert (G1: k >? k0 = false). { bdestruct(k >? k0); lia. }
      assert (G2: k0 >? k = false). { bdestruct(k0 >? k); lia. }
      rewrite G1, G2.
      reflexivity.
    + bdestruct (k >? k0); bdestruct (k0 >? k).
      * exfalso. lia.
      * unfold union.
        destruct (map_of_tree t2 k0) eqn:E.
        ** assert(G:= (map_of_tree_prop _ _ _ H5 _ _ E)).
           simpl in G.
           exfalso. lia.
        ** specialize (IHt1 k0 H6).
           unfold find in IHt1.
           destruct (map_of_tree t1 k0) eqn:E'.
           *** assumption.
           *** assumption.
      * unfold union.
        destruct (map_of_tree t1 k0) eqn:E.
        ** assert(G:= (map_of_tree_prop _ _ _ H4 _ _ E)).
           simpl in G.
           exfalso. lia.
        ** specialize (IHt2 k0 H7).
           unfold find in IHt2.
           destruct (map_of_tree t2 k0) eqn:E'.
           *** assumption.
           *** assumption.
      * exfalso. lia.
Qed.


Lemma insert_relate' : forall (V : Type) (k : key) (v : V) (t : tree V),
   BST t -> Abs' (insert k v t) = update (Abs' t) k v.
Proof. Admitted.

Lemma map_of_list_app : forall (V : Type) (el1 el2: list (key * V)),
   disjoint (map fst el1) (map fst el2) ->
   map_of_list (el1 ++ el2) = union (map_of_list el1) (map_of_list el2).
Proof. Admitted.

Lemma elements_relate' : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs' t.
Proof. Admitted.
