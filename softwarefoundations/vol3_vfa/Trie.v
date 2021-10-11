From Coq Require Import Strings.String. (* for manual grading *)
From Coq Require Import ZArith.
From Coq Require Import PArith.
From VFA Require Import Perm.
From VFA Require Import Maps.
Import FunctionalExtensionality.


Module Integers.

Inductive positive : Set :=
  | (* 1 + 2n *) xI : positive -> positive
  | (* 2n     *) xO : positive -> positive
  | (* 1      *) xH : positive.


Definition ten := xO (xI (xO xH)).

Fixpoint positive2nat (p: positive) : nat :=
  match p with
  | xI q => 1 + 2 * positive2nat q
  | xO q => 0 + 2 * positive2nat q
  | xH   => 1
 end.

Eval compute in positive2nat ten.

Fixpoint print_in_binary (p: positive) : list nat :=
  match p with
  | xI q => print_in_binary q ++ [1]
  | xO q => print_in_binary q ++ [0]
  | xH   =>  [1]
 end.
Eval compute in print_in_binary ten.


Notation "p ~ 1" := (xI p) (at level 7, left associativity, format "p '~' '1'").
Notation "p ~ 0" := (xO p) (at level 7, left associativity, format "p '~' '0'").
Print ten.

Fixpoint succ x :=
  match x with
    | p~1 => (succ p)~0
    | p~0 => p~1
    | xH  => xH~0
  end.

Fixpoint addc (carry: bool) (x y: positive) {struct x} : positive :=
  match carry, x, y with
    | false, p~1, q~1 => (addc true p q)~0
    | false, p~1, q~0 => (addc false p q)~1
    | false, p~1, xH  => (succ p)~0
    | false, p~0, q~1 => (addc false p q)~1
    | false, p~0, q~0 => (addc false p q)~0
    | false, p~0, xH  => p~1
    | false, xH,  q~1 => (succ q)~0
    | false, xH,  q~0 => q~1
    | false, xH,  xH  => xH~0
    | true,  p~1, q~1 => (addc true p q)~1
    | true,  p~1, q~0 => (addc true p q)~0
    | true,  p~1, xH  => (succ p)~1
    | true,  p~0, q~1 => (addc true p q)~0
    | true,  p~0, q~0 => (addc false p q)~1
    | true,  p~0, xH  => (succ p)~0
    | true,  xH,  q~1 => (succ q)~1
    | true,  xH,  q~0 => (succ q)~0
    | true,  xH,  xH  => xH~1
  end.
Definition add (x y: positive) : positive := addc false x y.



Lemma succ_correct: forall p,
   positive2nat (succ p) = S (positive2nat p).
Proof.
  intros. induction p; simpl.
  - rewrite IHp. lia.
  - lia.
  - reflexivity.
Qed.

Lemma addc_correct: forall (c: bool) (p q: positive),
   positive2nat (addc c p q) =
        (if c then 1 else 0) + positive2nat p + positive2nat q.
Proof.
  intros c p.
  generalize dependent c.
  induction p; simpl; intros.
  - destruct c.
    + destruct q.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite succ_correct. simpl.
        remember (positive2nat p) as p'.
        lia.
    + destruct q.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite succ_correct. simpl.
        remember (positive2nat p) as p'.
        lia.
  - destruct c.
    + destruct q.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite succ_correct. simpl.
        remember (positive2nat p) as p'.
        lia.
    + destruct q.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite IHp. simpl.
        remember (positive2nat p) as p'.
        remember (positive2nat q) as q'.
        lia.
      * simpl.
        remember (positive2nat p) as p'.
        lia.
  - destruct c.
    + destruct q.
      * simpl. rewrite succ_correct. simpl.
        remember (positive2nat q) as q'.
        lia.
      * simpl. rewrite succ_correct. simpl.
        remember (positive2nat q) as q'.
        lia.
      * simpl. reflexivity.
    + destruct q.
      * simpl. rewrite succ_correct. simpl.
        remember (positive2nat q) as q'.
        lia.
      * simpl.
        remember (positive2nat q) as q'.
        lia.
      * simpl. reflexivity.
Qed.

Theorem add_correct: forall (p q: positive),
   positive2nat (add p q) = positive2nat p + positive2nat q.
Proof.
  intros.
  unfold add.
  apply addc_correct.
Qed.

Inductive comparison : Set :=
    Eq : comparison | Lt : comparison | Gt : comparison.


Fixpoint compare x y {struct x}:=
  match x, y with
    | p~1, q~1 => compare p q
    | p~1, q~0 => match compare p q with 
                  | Lt => Lt 
                  | _  => Gt end
    | p~1, xH  => Gt
    | p~0, q~1 => match compare p q with 
                  | Gt => Gt 
                  | _  => Lt end
    | p~0, q~0 => compare p q
    | p~0, xH  => Gt
    | xH, q~1  => Lt
    | xH, q~0  => Lt
    | xH, xH   => Eq
  end.

Lemma positive2nat_pos:
 forall p, positive2nat p > 0.
Proof.
  intros.
  induction p; simpl; lia.
Qed.

Lemma positive_not_less_1: forall x, positive2nat x < 1 -> False.
Proof.
  intro x. induction x; simpl; intro HContra.
  - simpl in *. apply IHx. lia.
  - simpl in *. apply IHx. lia.
  - simpl in *. inversion HContra. lia.
Qed.

Lemma positive_geq_1: forall x, positive2nat x >= 1.
Proof.
  intro x. induction x; simpl.
  - lia.
  - lia.
  - lia.
Qed.

Theorem compare_correct:
 forall x y,
  match compare x y with
  | Lt => positive2nat x < positive2nat y
  | Eq => positive2nat x = positive2nat y
  | Gt => positive2nat x > positive2nat y
 end.
Proof.
  induction x; destruct y; simpl.
  - repeat (rewrite Nat.add_0_r).
    specialize (IHx y).
    destruct (compare x y).
    + rewrite Nat.succ_inj_wd. rewrite IHx. reflexivity.
    + rewrite <- Nat.succ_lt_mono. lia.
    + apply gt_n_S. lia.
  - repeat (rewrite Nat.add_0_r).
    specialize (IHx y).
    destruct (compare x y).
    + rewrite IHx. constructor.
    + lia.
    + lia.
  - repeat (rewrite Nat.add_0_r).
    specialize (IHx xH).
    destruct (compare x xH); simpl in *.
    + rewrite IHx. lia.
    + exfalso. apply (positive_not_less_1 x IHx).
    + lia.
  - repeat (rewrite Nat.add_0_r).
    specialize (IHx y).
    destruct (compare x y); lia.
  - repeat (rewrite Nat.add_0_r).
    specialize (IHx y).
    destruct (compare x y); lia.
  - repeat (rewrite Nat.add_0_r).
    assert (G:= positive_geq_1 x).
    lia.
  - assert (G:= positive_geq_1 y).
    lia.
  - assert (G:= positive_geq_1 y).
    lia.
  - reflexivity.
Qed.

Inductive Z : Set :=
  | Z0 : Z
  | Zpos : positive -> Z
  | Zneg : positive -> Z.

End Integers.


(* Trie *)

Inductive trie (A : Type) :=
    | Leaf : trie A
    | Node : trie A -> A -> trie A -> trie A.
Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Definition trie_table (A: Type) : Type := (A * trie A)%type.
Definition empty {A: Type} (default: A) : trie_table A :=
      (default, Leaf).

Fixpoint look {A: Type} (default: A) (i: positive) (m: trie A): A :=
    match m with
    | Leaf       => default
    | Node l x r =>
        match i with
        | xH    => x
        | xO i' => look default i' l
        | xI i' => look default i' r
        end
    end.

Definition lookup {A: Type} (i: positive) (t: trie_table A) : A :=
   look (fst t) i (snd t).


Fixpoint ins {A: Type} default (i: positive) (a: A) (m: trie A): trie A :=
    match m with
    | Leaf =>
        match i with
        | xH    => Node Leaf a Leaf
        | xO i' => Node (ins default i' a Leaf) default Leaf
        | xI i' => Node Leaf default (ins default i' a Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l a r
        | xO i' => Node (ins default i' a l) o r
        | xI i' => Node l o (ins default i' a r)
        end
    end.
Definition insert {A: Type} (i: positive) (a: A) (t: trie_table A)
                 : trie_table A :=
  (fst t, ins (fst t) i a (snd t)).


Definition three_ten : trie_table bool :=
 insert 3 true (insert 10 true (empty false)).
Eval compute in three_ten.
Eval compute in map (fun i => lookup i three_ten) [3;1;4;1;5]%positive.

(* Trie correctness TODO *)

Lemma look_leaf: forall A (a:A) j, 
  look a j Leaf = a.
Proof.
  intros.
  induction j.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma look_ins_same: forall {A} a k (v:A) t, 
  look a k (ins a k v t) = v.
Proof.
  intros A a k.
  induction k; simpl; intros.
  - destruct t.
    + apply IHk.
    + apply IHk.
  - destruct t.
    + apply IHk.
    + apply IHk.
  - destruct t.
    + reflexivity.
    + reflexivity.
Qed.

Lemma look_ins_other: forall {A} a j k (v:A) t,
   j <> k -> look a j (ins a k v t) = look a j t.
Proof.
  intros A a j.
  induction j; simpl; intros.
  - destruct k.
    + simpl.
      destruct t.
      * rewrite IHj.
        apply look_leaf.
        lia.
      * apply IHj.
        lia.
    + simpl.
      destruct t.
      * apply look_leaf.
      * reflexivity.
    + simpl.
      destruct t.
      * apply look_leaf.
      * reflexivity.
  - destruct k.
    + simpl.
      destruct t.
      * apply look_leaf.
      * reflexivity.
    + simpl.
      destruct t.
      * rewrite IHj.
        apply look_leaf.
        lia.
      * apply IHj.
        lia.
    + simpl.
      destruct t.
      * apply look_leaf.
      * reflexivity.
  - destruct k.
    + simpl.
      destruct t.
      * reflexivity.
      * reflexivity.
    + simpl.
      destruct t.
      * reflexivity.
      * reflexivity.
    + simpl.
      destruct t.
      * exfalso. apply H. lia.
      * exfalso. apply H. lia.
Qed.


Definition nat2pos (n: nat) : positive := Pos.of_succ_nat n.
Definition pos2nat (n: positive) : nat := pred (Pos.to_nat n).

Lemma pos2nat2pos: forall p, nat2pos (pos2nat p) = p.
Proof.
  intro. unfold nat2pos, pos2nat.
  rewrite <- (Pos2Nat.id p) at 2.
  destruct (Pos.to_nat p) eqn:?.
  pose proof (Pos2Nat.is_pos p). lia.
  rewrite <- Pos.of_nat_succ.
  reflexivity.
Qed.

Lemma nat2pos2nat: forall i, pos2nat (nat2pos i) = i.
Proof.
  intro. unfold nat2pos, pos2nat.
  rewrite SuccNat2Pos.id_succ.
  reflexivity.
Qed.

Lemma pos2nat_injective: forall p q, pos2nat p = pos2nat q -> p = q.
Proof.
  intros.
  rewrite <- pos2nat2pos.
  rewrite <- H.
  symmetry.
  apply pos2nat2pos.
Qed.

Lemma nat2pos_injective: forall i j, nat2pos i = nat2pos j -> i = j.
Proof.
  intros.
  rewrite <- nat2pos2nat.
  rewrite <- H.
  symmetry.
  apply nat2pos2nat.
Qed.


Definition is_trie {A: Type} (t: trie_table A) : Prop := True.

Definition abstract {A: Type} (t: trie_table A) (n: nat) : A :=
  lookup (nat2pos n) t.

Definition Abs {A: Type} (t: trie_table A) (m: total_map A) :=
  abstract t = m.


Theorem empty_is_trie: forall {A} (default: A), is_trie (empty default).
Proof.
Admitted.

Theorem insert_is_trie: forall {A} i x (t: trie_table A),
   is_trie t -> is_trie (insert i x t).
Proof.
Admitted.


Theorem empty_relate: forall {A} (default: A),
    Abs (empty default) (t_empty default).
Proof.
  intros.
  unfold Abs, abstract, t_empty.
  extensionality o.
  unfold lookup.
  simpl.
  apply look_leaf.
Qed.

Theorem lookup_relate: forall {A} i (t: trie_table A) m,
    is_trie t -> Abs t m -> lookup i t = m (pos2nat i).
Proof.
  intros.
  unfold Abs, abstract, t_empty in *.
  rewrite <- H0.
  rewrite pos2nat2pos.
  reflexivity.
Qed.

Theorem insert_relate: forall {A} k (v: A) t cts,
    is_trie t ->
    Abs t cts ->
    Abs (insert k v t) (t_update cts (pos2nat k) v).
Proof.
  intros.
  unfold Abs, abstract, t_empty, t_update in *.
  extensionality o.
  unfold lookup. destruct t. simpl.
  bdestruct (pos2nat k =? o).
  - rewrite <- H1.
    rewrite pos2nat2pos.
    apply look_ins_same.
  - rewrite <- H0.
    unfold lookup. simpl.
    apply look_ins_other.
    intros Hcontra.
    apply H1.
    rewrite <- pos2nat2pos in Hcontra.
    apply nat2pos_injective in Hcontra.
    symmetry.
    assumption.
Qed. 

Example Abs_three_ten:
    Abs
       (insert 3 true (insert 10 true (empty false)))
       (t_update (t_update (t_empty false) (pos2nat 10) true) (pos2nat 3) true).
Proof.
  try (apply insert_relate; [hnf; auto | ]).
  try (apply insert_relate; [hnf; auto | ]).
  try (apply empty_relate).
Qed.
