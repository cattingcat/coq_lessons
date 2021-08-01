From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Module Maps.

Locate "+".
Print Init.Nat.add.
Print string_dec.
Check string_dec.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.


Theorem eqb_string_refl : forall s : string, 
  true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
  eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
  - rewrite Hs_eq. split. reflexivity. reflexivity.
  - split.
    + intros contra. discriminate contra.
    + intros H. exfalso. apply Hs_not_eq. apply H.
Qed.

Locate not_true_iff_false.

Theorem eqb_string_false_iff : forall x y : string,
  eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. 
Qed.


Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A): total_map A :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof. unfold t_empty. intros. reflexivity. Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof. intros. unfold t_update. rewrite <- eqb_string_refl. simpl. reflexivity. Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof. unfold t_update, eqb_string. intros. 
  destruct (string_dec x1 x2) as [Hsd | Hsd].
  - exfalso. apply H. apply Hsd.
  - reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof. unfold t_update. intros.
  apply functional_extensionality.
  intros val.
  unfold eqb_string.
  destruct (string_dec x val) as [Hsd | Hsd].
  - reflexivity.
  - reflexivity.
Qed.

Print reflect.

Lemma eqb_stringP : forall x y : string,
  reflect (x = y) (eqb_string x y).
Proof. unfold eqb_string. intros. 
  destruct (string_dec x y) as [Exy | Exy].
  - apply ReflectT. apply Exy.
  - apply ReflectF. apply Exy.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof. unfold t_update. intros.
  apply functional_extensionality.
  intros val.
  destruct (eqb_stringP x val) as [E|E].
  - rewrite -> E. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof. intros.
  apply functional_extensionality.
  intros x.
  unfold t_update.
  destruct (eqb_stringP x1 x) as [E|E].
  - rewrite <- E.
    destruct (eqb_stringP x2 x1) as [E1|E1].
    + exfalso. apply H. apply E1.
    + reflexivity.
  - reflexivity.
Qed.



Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof. intros. unfold empty, t_empty. reflexivity. Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof. intros. unfold update, t_update. rewrite <- eqb_string_refl. reflexivity. Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof. intros. unfold update, t_update.
  destruct (eqb_stringP x2 x1) as [E|E].
  - exfalso. apply H. apply E.
  - reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof. intros. unfold update, t_update.
  apply functional_extensionality.
  intros val.
  destruct (eqb_stringP x val) as [E|E].
  - reflexivity.
  - reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof. intros. unfold update, t_update.
  apply functional_extensionality.
  intros val.
  destruct (eqb_stringP x val) as [E|E].
  - rewrite <- H. rewrite -> E. reflexivity.
  - reflexivity.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof. intros. unfold update, t_update.
  apply functional_extensionality.
  intros val.
  destruct (eqb_stringP x1 val) as [E|E].
  - destruct (eqb_stringP x2 val) as [E1|E1].
    + rewrite <- E in E1. exfalso. apply H. apply E1. 
    + reflexivity.
  - reflexivity.
Qed.

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma inclusion_update : forall (A : Type) (m m' : partial_map A) (x : string) (vx : A),
  inclusion m m' ->
  inclusion (x |-> vx ; m) (x |-> vx ; m').
Proof. unfold inclusion, update, t_update. intros. 
  destruct (eqb_stringP x x0) as [E|E].
  - apply H0.
  - apply H. apply H0.
Qed.

End Maps.