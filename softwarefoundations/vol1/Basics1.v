

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. 
  simpl. 
  reflexivity. 
Qed.


Theorem plus_O_n' : forall (n : nat), 0 + n = n.
Proof.
  intros n. 
  reflexivity. 
Qed.





Fixpoint even (n : nat) : bool :=
  match n with 
  | O => true
  | S O => false
  | S (S m) => even m
  end.


Theorem my_tst : forall (n : nat), (even n = true) -> (even (n - 2) = true).
Proof.
  (* Actually it is wrong *) Admitted.

(*
Proof.
  intros n. 
  simpl. 
  reflexivity. 
Qed.
*)




Theorem plus_id_example : forall (n m : nat),
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite <- H.
  (* rewrite -> H. *) (* rewrite direction -> <- *)
  reflexivity. 
Qed.




(* Ex *)
Theorem plus_id_exercise : forall (n m o : nat),
  n = m 
    -> 
      m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros G.
  rewrite -> H.
  rewrite <- G.
  reflexivity.
Qed.

(* Lemmas from lib*)
Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(*   ===> forall n m : nat, n * m + n = n * S m   *)


Theorem mult_n_0_m_0 : forall (p q : nat),
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O. (* Using lemmas to rewrite *)
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

(* Ex *)
Theorem mult_n_1 : forall (p : nat),
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.



Print mult_n_Sm.

Print mult_n_1.



(* Definition mult_n_1' : forall (p : nat), (p * 1 = p). *)



Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => eqb i j
  | _, _ => false
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0_firsttry : forall (n : nat),
  ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E. (* [..|..|..| - introduction names for each branch ]*)
                              (* E - is a name for hypothesis n = O or n = S n' *)
  - simpl. (* does nothing! *)
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Print plus_1_neq_0_firsttry.


Theorem andb_commutative : forall (b c : bool), andb b c = andb c b.
Proof.
  intros b c. 
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.


Theorem andb_true_elim2 : forall (b c : bool),
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl.
    intros H.
    rewrite -> H.
    reflexivity.
  - simpl.
    intros H.
    destruct c eqn:Ec.
    * reflexivity.
    * rewrite -> H.
      reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall (n : nat),
  0 =? (n + 1) = false.
Proof.
  intros []. (* Short syntax for intros & destruct *)
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.


Theorem neg_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = negb x) 
  ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.



Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) 
  ->
  b = c.
Proof.
  intros b c.
  destruct b eqn:Hb.
  - simpl.
    intros H.
    rewrite <- H.
    reflexivity.
  - simpl.
    intros H.
    rewrite <- H.
    reflexivity.
Qed.





Module BinNat.
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (b : bin) : bin :=
  match b with
  | Z => B1 Z
  | B0 i => B1 i
  | B1 i => B0 (incr i)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 i => 2 * (bin_to_nat i)
  | B1 i => 1 + 2 * (bin_to_nat i)
  end.


Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.


End BinNat.




