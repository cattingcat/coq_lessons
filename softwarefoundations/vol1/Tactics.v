Module Tactics.
From LF Require Export Poly.
From LF Require Export Lists.
From LF Require Export Basics1.
From LF Require Export Basics.
From LF Require Export Induction.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint even (n : nat) : bool :=
  match n with 
  | O => true
  | S O => false
  | S (S m) => even m
  end.
Definition odd (n : nat) := negb (even n).




Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. (* rewrite -> eq. refl. *)
Qed.


Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> ([n;o] = [m;p])) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.



Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p H1 H2 H3.
  apply H2.
  apply H1.
  apply H3.
Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. (* swap in eq clause *)
  apply H. 
Qed.



Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof. 
  intros X l. 
  induction l as [| h t H ].
  - reflexivity. 
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| h t H ].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| h t H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| h t H ].
  - simpl.
    rewrite -> app_nil_r.
    reflexivity.
  - simpl.
    rewrite -> H.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h t H ].
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite -> H.
    simpl.
    reflexivity.
Qed.

Theorem rev_exercise1 : forall (X: Type) (l l' : list X),
  l = rev l' ->
  l' = rev l.
Proof.
  intros X l l' H.
  symmetry.
  rewrite -> H.
  apply rev_involutive.
Qed.





Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.

Definition minustwo (n : nat) : nat :=
  match n with
  | S (S n') => n'
  | _ => O
  end.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity m.
  apply eq2.
  apply eq1.
Qed.







Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. (* Removes layer of ctors *)
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1.
  injection H1 as H1' H1''.
  rewrite <- H1''.
  intros H2.
  injection H2 as H2'.
  transitivity z.
  apply H1'.
  symmetry.
  apply H2'.
Qed.





Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. 
  discriminate contra. 
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. 
  discriminate contra. 
Qed.



Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H.
  discriminate H.
Qed.








Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => eqb i j
  | _, _ => false
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.


Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n' ] eqn:E.
  - reflexivity.
  - simpl.
    intros H.
    discriminate H.
Qed.


Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.






Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. 
  simpl in H. 
  apply H. 
Qed.


Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H. Qed.



Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
      Abort.


Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    intros m.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + simpl.
      intros H.
      discriminate H.
  - intros m.
    destruct m as [| m'] eqn:E.
    + simpl.
      intros G.
      discriminate G.
    + 
      intros G.
      apply f_equal.
      simpl in G.
      injection G as G'.
      apply H.
      apply G'.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' H].
  - intros m.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + simpl.
      intros G.
      discriminate G.
  - intros m.
    destruct m as [| m'] eqn:E.
    + simpl.
      intros G.
      discriminate G.
    + simpl.
      intros G.
      apply f_equal.
      apply H.
      apply G.
Qed.



Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.


Fixpoint nth_error {X : Type} (l : list X) (n : nat): option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  generalize dependent X.
  induction l as [| h t H ].
  - simpl.
    intros n H'.
    reflexivity.
  - simpl.
    intros n G.
    destruct n as [| n'] eqn:E.
    + discriminate G.
    + injection G as G'.
      apply H.
      apply G'.
Qed.


Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | []          => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y): list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| (x, y) t H ].
  - simpl. 
    intros l1 l2 G.
    injection G as G'.
    rewrite <- G'.
    rewrite <- H.
    simpl.
    reflexivity.
  - simpl.
    unfold combine.
    intros l1 l2 G.
    destruct (split t) eqn:E.
    injection G as G'1 G'2.
    rewrite <- G'1.
    rewrite <- G'2.
    rewrite -> H.
    reflexivity.
    reflexivity.
Qed.




Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.


Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - (* e3 = true *) 
    apply eqb_true in Heqe3.
    rewrite -> Heqe3. 
    reflexivity.
  - (* e3 = false *)
    destruct (n =? 5) eqn:Heqe5.
    + (* e5 = true *)
      apply eqb_true in Heqe5.
      rewrite -> Heqe5. 
      reflexivity.
    + (* e5 = false *) 
      discriminate eq.
Qed.


Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  destruct b eqn:B.
  - destruct (f true) eqn:FTrue.
    + rewrite -> FTrue.
      rewrite -> FTrue.
      reflexivity.
    + destruct (f false) eqn:FFalse.
      * apply FTrue.
      * apply FFalse.
  - destruct (f false) eqn:FFalse.
    + destruct (f true) eqn:FTrue.
      * apply FTrue.
      * apply FFalse.
    + rewrite -> FFalse.
      rewrite -> FFalse.
      reflexivity.
Qed.








Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [| n' H ].
  - intros m.
    destruct m eqn:M.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - intros m.
    destruct m eqn:M.
    + simpl.
      reflexivity.
    + simpl.
      apply H.
Qed.

Lemma eqb_refl : forall n, n =? n = true.
Proof.
  intros n.
  induction n as [| n' H].
  - reflexivity.
  - simpl.
    apply H.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p H G.
  rewrite -> (eqb_true n m H).
  rewrite -> (eqb_true m p G).
  apply eqb_refl.
Qed.





Lemma len0_is_empty: forall (X: Type) (l: list X), length l = 0 -> l = [].
Proof.
  intros X l LenH.
  destruct l as [| h t ] eqn:E.
  - reflexivity.
  - simpl in LenH.
    discriminate LenH.
Qed.


Definition split_combine_statement : Prop := 
  forall (X Y: Type) (l: list (X*Y)) (l1: list X) (l2: list Y) (H: length l1 = length l2), combine l1 l2 = l -> split l = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l.
  induction l as [| (x,y) ltail H ].
  - intros l1 l2 HLen HComb.
    simpl.
    destruct l1 eqn:L1E.
    + simpl in HLen.
      symmetry in HLen.
      rewrite -> (len0_is_empty Y l2 HLen).
      reflexivity.
    + destruct l2 eqn:L2E.
      * simpl in HLen.
        discriminate HLen.
      * simpl in HComb.
        discriminate HComb.
  - intros l1 l2 HLen HComb.
    simpl.
    destruct l1 eqn:L1E.
    + simpl in HComb. 
      discriminate HComb.
    + destruct l2 eqn:L2E.
      * simpl in HLen.
        discriminate HLen.
      * simpl in HComb.
        injection HComb as HComb'1 HComb'2 HComb'3.
(*        destruct (split ltail) eqn:E.*)
        rewrite -> HComb'1.
        rewrite -> HComb'2.
        rewrite -> HComb'1 in L1E.
        rewrite -> HComb'2 in L2E.
        simpl in HLen.
        injection HLen as HLen'.
        rewrite -> (H l l0 HLen' HComb'3).
        reflexivity.
Qed.



Fixpoint filter {X: Type} (test: X -> bool) (l: list X) : list X :=
  match l with
  | []     => []
  | h :: t =>
    if test h 
    then h :: (filter test t)
    else filter test t
  end.


Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l.
  generalize dependent x.
  generalize dependent X.
  induction l as [| lh lt LH ].
  - simpl.
    intros x lf H.
    discriminate H.
  - destruct (test lh) eqn:TstLh.
    + simpl.
      rewrite -> TstLh.
      intros x lf HH.
      injection HH as HH'.
      rewrite <- HH'.
      apply TstLh.
    + simpl.
      rewrite -> TstLh.
      apply LH.
Qed.




Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => true
  | cons h t => if test h then forallb test t else false
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.


Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => false
  | cons h t => if test h then true else existsb test t
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool := 
  negb (forallb (fun i => negb (test i)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. 
  intros X test l.
  induction l as [| lh lt LH ].
  - unfold existsb'.
    simpl.
    reflexivity.
  - destruct (test lh) eqn:E.
    + unfold existsb'.
      simpl.
      rewrite -> E.
      simpl.
      reflexivity.
    + unfold existsb'.
      simpl.
      rewrite -> E.
      simpl.
      rewrite -> LH.
      unfold existsb'.
      reflexivity.
Qed.


End Tactics.
