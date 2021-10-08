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
From VFA Require Import SearchTree.


Module Type Table.
  Parameter table : Type.
  Definition key := nat.
  Parameter V : Type.
  Parameter default : V.
  Parameter empty : table.
  Parameter get : key -> table -> V.
  Parameter set : key -> V -> table -> table.
  Axiom get_empty_default : forall (k : key), get k empty = default.
  Axiom get_set_same : forall (k : key) (v : V) (t : table), get k (set k v t) = v.
  Axiom get_set_other : forall (k k' : key) (v : V) (t : table), k <> k' -> get k' (set k v t) = get k' t.
End Table.



Module Type ValType.
  Parameter V : Type.
  Parameter default : V.
End ValType.

Module FunTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := key -> V.
  Definition empty : table := fun _ => default.
  Definition get (k : key) (t : table) : V := t k.
  Definition set (k : key) (v : V) (t : table) : table :=
    fun k' => if k =? k' then v else t k'.
  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof. intros. unfold get, empty. reflexivity. Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof. intros. unfold get, set. bdall. Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof. intros. unfold get, set. bdall. Qed.
End FunTable.



Module StringVal.
  Definition V := string.
  Definition default := ""%string.
End StringVal.

Module FunTableExamples.
  Module StringFunTable := FunTable StringVal.
  Import StringFunTable.
  Open Scope string_scope.

  Example ex1 : get 0 empty = "".
  Proof. reflexivity. Qed.

  Example ex2 : get 0 (set 0 "A" empty) = "A".
  Proof. reflexivity. Qed.

  Example ex3 : get 1 (set 0 "A" empty) = "".
  Proof. reflexivity. Qed.
End FunTableExamples.


Module NatFunTableExamples.
  Module NatVal.
    Definition V := nat.
    Definition default := 0.
  End NatVal.

  Module NatFunTable := FunTable NatVal.
  Import NatFunTable.

  Example ex1 : get 0 empty = 0.
  Proof. reflexivity. Qed.

  Example ex2 : get 0 (set 0 1 empty) = 1.
  Proof. reflexivity. Qed.

  Example ex3 : get 1 (set 0 1 empty) = 0.
  Proof. reflexivity. Qed.
End NatFunTableExamples.



Module ListsTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := list (key * V).
  Definition empty : table := [].
  Fixpoint get (k : key) (t : table) : V :=
    match t with 
    | [] => default
    | (k', v) :: t' => if k =? k' then v else get k t'
    end.

  Definition set (k : key) (v : V) (t : table) : table :=
    (k, v) :: t.

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof. reflexivity. Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof. intros. simpl. 
    bdestruct (k' =? k).
    - exfalso. auto.
    - reflexivity.
  Qed.
End ListsTable.



Module StringListsTableExamples.
  Module StringListsTable := ListsTable StringVal.
  Import StringListsTable.
  Open Scope string_scope.
  Example ex1 : get 0 empty = "".
  Proof. reflexivity. Qed.
  Example ex2 : get 0 (set 0 "A" empty) = "A".
  Proof. reflexivity. Qed.
  Example ex3 : get 1 (set 0 "A" empty) = "".
  Proof. reflexivity. Qed.
End StringListsTableExamples.



Module TreeTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := tree V.
  Definition empty : table := @empty_tree V.
  Definition get (k : key) (t: table) : V := lookup default k t.
  Definition set (k : key) (v : V) (t : table) : table := insert k v t.

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof.
    apply lookup_empty. Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof.
    intros. unfold get, set. apply lookup_insert_eq. Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof.
    intros. unfold get, set. apply lookup_insert_neq. assumption. Qed.
End TreeTable.


(* The : syntax makes the module type opaque: only what is revealed 
    in the type is available for code outside the module to use. 
    The <: syntax, however, makes the module type transparent: the module must 
    conform to the type, but everything about the module is still revealed. *)

(* Module TreeETableEncapsulated (VT : ValType) : (ETable 
    with Definition V := VT.V 
    with Definition default := VT.default). *)

Definition even_nat := {x : nat | Nat.Even x}.

Print ex. (* Sigma type for Prop *)
Print sigT. (* Sigma for Type *)
Print sig.

Definition search_tree (V : Type) := {t : tree V | BST t}.

Module SearchTreeTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := search_tree V.
  Definition empty : table := @exist (tree V) BST E (empty_tree_BST V).
  Definition get (k : key) (t : table) : V := 
    match t with 
    | exist _ t' pt => lookup default k t'
    end.

  Definition set (k : key) (v : V) (t : table) : table :=
    match t with 
    | exist _ t' pt => exist BST (insert k v t') (insert_BST V k v t' pt)
    end.

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof. reflexivity. Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof. intros. unfold get, set. simpl. destruct t. rewrite lookup_insert_eq. reflexivity. Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof.
    intros. unfold get, set. destruct t.
    apply lookup_insert_neq.
    assumption.
  Qed.
End SearchTreeTable.



Definition vector (X : Type) :=
  { '(xs, n) : list X * nat | length xs = n }.

Example a_vector : vector nat.
Proof.
  exists (1::2::3::[], 3).
  reflexivity.
Qed.

Definition vector_cons {X : Type} (x : X) (v : vector X) : vector X.
Proof.
  intros.
  destruct v.
  destruct x0.
  exists (x :: l, S n).
  simpl. rewrite y. reflexivity.
Defined.


Definition list_of_vector {X : Type} (v : vector X) : list X :=
  fst (proj1_sig v).

Theorem vector_cons_correct : forall (X : Type) (x : X) (v : vector X),
    list_of_vector (vector_cons x v) = x :: (list_of_vector v).
Proof.
  intros.
  destruct v.
  destruct x0.
  unfold list_of_vector. 
  simpl. (* Defined. is important for simpl !!! *)
  reflexivity.
Qed.

Definition vector_app {X : Type} (v1 v2 : vector X) : vector X.
Proof.
  intros.
  destruct v1, v2.
  destruct x, x0.
  exists (l ++ l0, n + n0).
  rewrite app_length.
  rewrite y, y0.
  reflexivity.
Defined.

Theorem vector_app_correct : forall (X : Type) (v1 v2 : vector X),
    list_of_vector (vector_app v1 v2) = list_of_vector v1 ++ list_of_vector v2.
Proof.
  intros.
  destruct v1, v2.
  destruct x, x0.
  unfold list_of_vector.
  simpl.
  reflexivity.
Qed.



Module Type ETableSubset.
  Include Table.
  Parameter bound : key -> table -> bool.
  Parameter elements : table -> list (key * V).
  Axiom bound_empty : forall (k : key),
      bound k empty = false.
  Axiom bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.
  Axiom bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
  Axiom elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Axiom elements_correct : forall (k : key) (v : V) (t : table),
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
End ETableSubset.

Module TreeETableSubset (VT : ValType) <: ETableSubset.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := { t : tree V | BST t }.
  Definition empty : table.
  Proof.
    apply (exist _ empty_tree).
    apply empty_tree_BST.
  Defined.

  Definition get (k : key) (t : table) : V :=
    lookup default k (proj1_sig t).

  Definition set (k : key) (v : V) (t : table) : table.
  Proof.
    destruct t as [t Ht].
    apply (exist _ (insert k v t)).
    apply insert_BST. assumption.
  Defined.

  Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k (proj1_sig t).

  Definition elements (t : table) : list (key * V) :=
    elements (proj1_sig t).

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof.
    apply lookup_empty.  Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof.
    intros. unfold get, set.
    destruct t as [t Hbst]. simpl.
    apply lookup_insert_eq.
  Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof.
    intros. unfold get, set.
    destruct t as [t Hbst]. simpl.
    apply lookup_insert_neq. assumption.
  Qed.

  Theorem bound_empty : forall (k : key),
      bound k empty = false.
  Proof. reflexivity. Qed.

  Theorem bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.
  Proof.
    intros k v t. unfold bound, set.
    destruct t as [t Hbst]. simpl in *.
    induction t; inv Hbst; bdall.
  Qed.

  Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
  Proof.
    intros k k' v t Hneq. unfold bound, set.
    destruct t as [t Hbst]. simpl in *.
    apply bound_insert_neq; auto.
  Qed.

  Theorem elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Proof.
    intros k v t Hbound Hlookup.
    pose proof SearchTree.elements_complete as Hcomplete. (* !!! *)
    unfold elements_complete_spec in Hcomplete.
    apply Hcomplete with default; try assumption.
  Qed.

  Theorem elements_correct : forall (k : key) (v : V) (t : table),
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
  Proof.
    intros k v t. simpl. intros Hin.
    pose proof SearchTree.elements_correct as Hcorrect.
    unfold elements_correct_spec in Hcorrect.
    apply Hcorrect; try assumption.
    destruct t as [t Hbst]. simpl. assumption.
  Qed.
End TreeETableSubset.