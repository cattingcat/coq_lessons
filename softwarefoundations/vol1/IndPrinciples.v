Module IndPrinciples.

Print nat_ind.
Check nat_ind :
  forall (P : nat -> Prop),
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

Theorem mul_0_r' : forall (n : nat),
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. Qed.


Theorem plus_one_r' : forall (n : nat),
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite -> H. reflexivity.
Qed.


Inductive rgb : Type :=
  | red
  | green
  | blue.

Check rgb_ind: 
  forall (P: rgb -> Prop),
  P red ->
  P green ->
  P blue ->
  forall (c : rgb), P c.


Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind :
  forall (P : natlist -> Prop),
    P nnil ->
    (forall (n : nat) (l : natlist),  P l -> P (ncons n l)) ->
    forall (l : natlist), P l.


Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

Check natlist'_ind :
  forall (P : natlist' -> Prop),
    P nnil' ->
    (forall (l : natlist'), P l -> forall (n : nat), P (nsnoc l n)) ->
    forall (n : natlist'), P n.



Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

Check booltree_ind: 
  forall (P : booltree -> Prop),
    P bt_empty ->
    (forall (b : bool), P (bt_leaf b)) ->
    (forall (b : bool) (t1: booltree), P t1 -> forall (t2 : booltree), P t2 -> P (bt_branch b t1 t2)) ->
    (forall (t : booltree), P t).


Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).

Check tree_ind: 
  forall (X: Type) (P: tree X -> Prop),
    (forall (x: X), P (leaf X x)) ->
    (forall (t1: tree X), P t1 -> forall (t2: tree X), P t2 -> P (node X t1 t2)) ->
    (forall (t: tree X), P t).


Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

Check foo'_ind: 
  forall (X: Type) (P: foo' X -> Prop),
    (forall (l: list X) (f: foo' X), P f -> P (C1 X l f)) ->
    P (C2 X ) ->
    (forall (f: foo' X), P f).



Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mul_0_r'' : forall (n: nat),
  P_m0r' n.
Proof.
  apply (nat_ind P_m0r').
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Note the proof state at this point! *)
    intros n IHn.
    unfold P_m0r' in IHn. unfold P_m0r'. simpl. apply IHn. Qed.

(* IndProp induction: *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n: nat) (H: ev n): ev (S (S n))
.

Check ev_ind :
  forall (P : nat -> Prop),
    P 0 ->
    (forall (n : nat), ev n -> P n -> P (S (S n)) ) ->
    (forall (n : nat), ev n -> P n).

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply (ev_ind ev').
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.



Inductive le1 : nat -> nat -> Prop :=
  | le1_n : forall n, le1 n n
  | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).
Notation "m <=1 n" := (le1 m n) (at level 70).

Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).
Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind :
  forall (P : nat -> nat -> Prop),
    (forall (n : nat), P n n) ->
    (forall (n m : nat), n <=1 m -> P n m -> P n (S m)) ->
    (forall (n n0 : nat), n <=1 n0 -> P n n0).

Check le2_ind :
  forall (n : nat) (P : nat -> Prop),
    P n ->
    (forall (m  : nat), n <=2 m -> P m -> P (S m)) ->
    (forall (n0 : nat), n <=2 n0 -> P n0).


(* induction lemma is just lemma *)
Fixpoint build_proof
         (P : nat -> Prop)
         (evPO : P 0)
         (evPS : forall (n : nat), P n -> P (S n))
         (n : nat) : P n :=
  match n with
  | 0   => evPO
  | S k => evPS k (build_proof P evPO evPS k)
  end.



Definition nat_ind2 :
  forall (P : nat -> Prop),
  P 0 ->
  P 1 ->
  (forall (n : nat), P n -> P (S(S n))) ->
  (forall (n : nat), P n) :=
    fun P P0 P1 PSS =>
      fix f (n:nat) := match n with
                       | 0        => P0
                       | 1        => P1
                       | S (S n') => PSS n' (f n')
                       end.

Fixpoint even (n: nat): bool :=
  match n with 
  | 0 => true
  | S 0 => false
  | S (S k) => even k
  end.

Lemma even_ev : forall n, even n = true -> ev n.
Proof.
  intros.
  induction n as [ | |n'] using nat_ind2.
  - apply ev_0.
  - simpl in H.
    inversion H.
  - simpl in H.
    apply ev_SS.
    apply IHn'.
    apply H.
Qed.







End IndPrinciples.