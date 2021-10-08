From Coq Require Import String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import ZArith.
From VFA Require Import Perm.
From VFA Require Import Extract.

Open Scope Z_scope.


Section ValueType.
  Variable V : Type.
  Variable default : V.

  Definition key := int.

  Inductive color := Red | Black.

  Inductive tree : Type :=
  | E : tree
  | T : color -> tree -> key -> V -> tree -> tree.

  Definition empty_tree : tree := E.

  Fixpoint lookup (x: key) (t : tree) : V :=
    match t with
    | E => default
    | T _ tl k v tr => if ltb x k then lookup x tl
                      else if ltb k x then lookup x tr
                           else v
    end.

   Definition balance (rb : color) (t1 : tree) (k : key) (vk : V) (t2 : tree) : tree :=
    match rb with
    | Red => T Red t1 k vk t2
    | _ => match t1 with
          | T Red (T Red a x vx b) y vy c =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
          | T Red a x vx (T Red b y vy c) =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
          | _ => match t2 with
                | T Red (T Red b y vy c) z vz d =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | T Red b y vy (T Red c z vz d) =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | _ => T Black t1 k vk t2
                end
          end
    end.

  Fixpoint ins (x : key) (vx : V) (t : tree) : tree :=
    match t with
    | E => T Red E x vx E
    | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                      else if ltb y x then balance c a y vy (ins x vx b)
                           else T c a x vx b
    end.

  Definition make_black (t : tree) : tree :=
    match t with
    | E => E
    | T _ a x vx b => T Black a x vx b
    end.

  Definition insert (x : key) (vx : V) (t : tree) := make_black (ins x vx t).

  Fixpoint elements_tr (t : tree) (acc: list (key * V)) : list (key * V) :=
    match t with
    | E => acc
    | T _ l k v r => elements_tr l ((k, v) :: elements_tr r acc)
    end.

  Definition elements (t : tree) : list (key * V) := elements_tr t [].



  Lemma ins_not_E : forall (x : key) (vx : V) (t : tree),
      ins x vx t <> E.
  Proof.
    intros. destruct t; simpl.
    discriminate.
    (* Let's destruct on the topmost case, ltb x k. We can use
       destruct instead of bdestruct because we don't need to know
       whether x < k or x ≥ k. *)
    destruct (ltb x k).
    unfold balance.
    (* A huge goal!  The proof of this goal begins by matching
       against a color. *)
    destruct c.
    discriminate.
    (* Another match, this time against a tree. *)
    destruct (ins x vx t1).
    (* Another match against a tree. *)
    destruct t2.
    discriminate.
    (* Yet another match. This pattern deserves automation.  The
       following tactic applies destruct whenever the current goal
       is a match against a color or a tree. *)

    match goal with
    | |- match ?c with Red => _ | Black => _ end <> _ => destruct c
    | |- match ?t with E => _ | T _ _ _ _ _ => _ end <> _=> destruct t
    end.
    (* Let's apply that tactic repeatedly. *)
    repeat
      match goal with
      | |- match ?c with Red => _ | Black => _ end <> _ => destruct c
      | |- match ?t with E => _ | T _ _ _ _ _ => _ end <> _=> destruct t
      end.
    (* Now we're down to a base case. *)
    discriminate.
    (* And another base case. We could match against those, too. *)
    match goal with
    | |- T _ _ _ _ _ <> E => discriminate
    end.
    (* Let's restart the proof to incorporate this automation. *)
  Abort.

  Lemma ins_not_E : forall (x : key) (vx : V) (t : tree),
      ins x vx t <> E.
  Proof.
    intros. destruct t; simpl.
    - discriminate.
    - unfold balance.
      repeat
        match goal with
        | |- (if ?x then _ else _) <> _ => destruct x
        | |- match ?c with Red => _ | Black => _ end <> _=> destruct c
        | |- match ?t with E => _ | T _ _ _ _ _ => _ end <> _=> destruct t
        | |- T _ _ _ _ _ <> E => discriminate
        end.
  Qed.



  Fixpoint ForallT (P: int -> V -> Prop) (t: tree) : Prop :=
    match t with
    | E           => True
    | T c l k v r => P k v /\ ForallT P l /\ ForallT P r
    end.

  Inductive BST : tree -> Prop :=
  | ST_E : BST E
  | ST_T : forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (T c l k v r).

  Lemma empty_tree_BST: BST empty_tree.
  Proof.
    unfold empty_tree. constructor.
  Qed.


 Lemma balance_BST: forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (balance c l k v r).
  Proof.
    intros c l k v r PL PR BL BR. unfold balance.
    repeat
      match goal with
      | |- BST (match ?c with Red => _ | Black => _ end) => destruct c
      | |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end) => destruct t
      end.
  Abort.

  Lemma balance_BST: forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (balance c l k v r).
  Proof.
    intros. unfold balance.
    repeat
      (match goal with
       | |- BST (match ?c with Red => _ | Black => _ end) => destruct c
       | |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end) => destruct t
       | |- ForallT _ (T _ _ _ _ _) => repeat split
       | H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
       | H: BST (T _ _ _ _ _) |- _ => inv H
       end;
       (try constructor; auto; try lia)).
  Abort.


  Lemma ForallT_imp : forall (P Q : int -> V -> Prop) t,
      ForallT P t ->
      (forall k v, P k v -> Q k v) ->
      ForallT Q t.
  Proof.
    induction t; intros.
    - auto.
    - destruct H as [? [? ?]]. repeat split; auto.
  Qed.

  Lemma ForallT_greater : forall t k k0,
      ForallT (fun k' _ => Abs k' > Abs k) t ->
      Abs k > Abs k0 ->
      ForallT (fun k' _ => Abs k' > Abs k0) t.
  Proof.
    intros. eapply ForallT_imp; eauto.
    intros. simpl in H1. lia.
  Qed.

  Lemma ForallT_less : forall t k k0,
      ForallT (fun k' _ => Abs k' < Abs k) t ->
      Abs k < Abs k0 ->
      ForallT (fun k' _ => Abs k' < Abs k0) t.
  Proof.
    intros; eapply ForallT_imp; eauto.
    intros. simpl in H1. lia.
  Qed.


  Lemma balance_BST: forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (balance c l k v r).
  Proof.
    intros. unfold balance.
    repeat
      (match goal with
       | |- BST (match ?c with Red => _ | Black => _ end) => destruct c
       | |- BST (match ?s with E => _ | T _ _ _ _ _ => _ end) => destruct s
       | |- ForallT _ (T _ _ _ _ _) => repeat split
       | H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
       | H: BST (T _ _ _ _ _) |- _ => inv H
       end;
       (try constructor; auto; try lia)).
    (* all: t applies t to every subgoal. *)
    all: try eapply ForallT_greater; try eapply ForallT_less; eauto; try lia.
  Qed.


  Lemma balanceP : forall (P : key -> V -> Prop) (c : color) (l r : tree) (k : key) (v : V),
      ForallT P l ->
      ForallT P r ->
      P k v ->
      ForallT P (balance c l k v r).
  Proof.
    intros. unfold balance.
    repeat
      (match goal with
       | |- ForallT P (match ?c with Red => _ | Black => _ end) => destruct c
       | |- ForallT P (match ?s with E => _ | T _ _ _ _ _ => _ end) => destruct s
       | H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
       end; try (constructor; auto); try assumption).
  Qed.

  Lemma insP : forall (P : key -> V -> Prop) (t : tree) (k : key) (v : V),
      ForallT P t ->
      P k v ->
      ForallT P (ins k v t).
  Proof.
    intros. 
    induction t.
    - unfold ins. simpl. auto.
    - simpl. unfold balance.
      inversion H; subst.
      destruct H2 as [Hl Hr].
      repeat
        (match goal with
        | H: ?a, G: ?a -> ?b |- _ => apply G in H
        end).
      repeat
        (match goal with
         | |- ForallT P (if ?c then _ else _) => destruct c
         | |- ForallT P (match ?c with Red => _ | Black => _ end) => destruct c
         | |- ForallT P (match ?s with E => _ | T _ _ _ _ _ => _ end) => destruct s
         | H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
         end; try (constructor; auto); try assumption).
      all: simpl; repeat split; try assumption.
  Qed.

  Lemma ins_BST : forall (t : tree) (k : key) (v : V),
      BST t ->
      BST (ins k v t).
  Proof.
    intros.
    induction H.
    - simpl. constructor; simpl; auto; constructor.
    - simpl.
      bdestruct (ltb k k0); bdestruct (ltb k0 k).
      + exfalso. lia.
      + apply balance_BST; try assumption.
        apply insP; try assumption.
      + apply balance_BST; try assumption.
        apply insP; try assumption.
        lia.
      + constructor; try assumption.
        * eapply ForallT_imp.
          apply H. intros. simpl in *. lia.
        * eapply ForallT_imp.
          apply H0. intros. simpl in *. lia.
  Qed.

  Theorem make_black_BST : forall t,
      BST t <->
      BST (make_black t).
  Proof.
    intros. unfold make_black.
    split.
    * intro H. destruct t.
      - constructor.
      - inversion H.
        constructor; assumption.
    * intro H. destruct t.
      - constructor.
      - inversion H.
        constructor; assumption.
  Qed.

  Theorem insert_BST : forall t v k,
      BST t ->
      BST (insert k v t).
  Proof.
    intros.
    induction H.
    - unfold insert. simpl. constructor; simpl; auto; constructor.
    - unfold insert in *. simpl.
      rewrite <- make_black_BST in *.
      bdestruct (ltb k k0); bdestruct (ltb k0 k).
      + exfalso. lia.
      + apply balance_BST; simpl; try assumption.
        * apply insP; auto.
      + apply balance_BST; simpl; try assumption.
        * apply insP; auto. lia.
      + constructor; try assumption.
        * eapply (ForallT_imp _ _ _ H).
          intros. lia.
        * eapply (ForallT_imp _ _ _ H0).
          intros. lia.
  Qed.


(* Verification TODO *)

End ValueType.
