Module NatList.
From LF Require Import Tst.
From LF Require Import Tst.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.


Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. 
  destruct p as [n m]. 
  simpl. 
  reflexivity. 
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.




Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).


Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
(*
Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

1 + 2 :: [3]
    50 < 60
(1 + 2) :: [3]
*)


Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Print mylist2.


Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.


Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | cons x _ => x
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | cons _ t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.




Fixpoint nonzeros (l:natlist) : natlist :=
  match l with 
  | nil => nil
  | cons O t => nonzeros t
  | cons n t => n :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S (S n') => even n'
  | S n' => false
  end. 

Definition odd (n : nat) : bool := negb (even n).

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | cons i t => if odd i then i :: (oddmembers t) else oddmembers t
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat := length (oddmembers l).
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. unfold countoddmembers. simpl. reflexivity. Qed. 

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. unfold countoddmembers. simpl. reflexivity. Qed. 

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. unfold countoddmembers. simpl. reflexivity. Qed. 



Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | l1, nil => l1
  | nil, l2 => l2
  | cons a1 t1, cons a2 t2 => a1 :: a2 :: alternate t1 t2
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.








Definition bag := natlist.

Print nat.

Fixpoint eqn (a : nat) (b : nat) : bool :=
  match a, b with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S a', S b' => eqn a' b'
  end.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | cons h t => if (eqn h v) then S (count v t) else count v t
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.



Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | nil => false
  | cons h t => if eqn v h then true else member v t
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.



Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | cons h t => if eqn h v then t else h :: (remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | cons h t => if eqn h v then remove_all v t else h :: (remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.


Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | cons h t => if member h s2 then subset t (remove_one h s2) else false
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem bag_theorem : forall (b : bag) (n: nat), 
  length (add n b) = S (length b).
Proof.
  intros b n.
  simpl.
  reflexivity.
Qed.







Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. 
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. 
    rewrite -> IHl1'. 
    reflexivity. 
Qed.


Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.













Theorem add_0_r_firsttry : forall (n : nat),
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    intros m.
    simpl.
    rewrite -> add_0_r_firsttry.
    reflexivity.
  - simpl.
    intros m.
    rewrite <- plus_n_Sm.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.





Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. 
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. 
    rewrite -> IHl1'. 
    reflexivity. 
Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> app_length.
    simpl.
    rewrite <- IHl'.
    rewrite add_comm.
    simpl.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l.
  induction l as [| h t H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> app_length.
    simpl.
    rewrite -> add_comm.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.

Search rev.
Search (_ + _ = _ + _).
Search (?x + ?y = ?y + ?x).


Lemma cons_tst : forall (l m : natlist) (v : nat), 
  (v :: l) ++ m = v :: (l ++ m).
Proof.
  intros l m v.
  induction l as [| h t H ].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| h t H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| h t H ].
  - simpl.
    rewrite -> app_nil_r.
    reflexivity.
  - simpl.
    rewrite -> H.
    rewrite -> app_assoc.
    reflexivity.
Qed.



Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| h t H ].
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite -> H.
    simpl.
    reflexivity.
Qed.


Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons h1 t1, cons h2 t2 => if eqn h1 h2 then eqblist t1 t2 else false
  | _, _ => false
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Lemma eqn_refl: forall n : nat, eqn n n = true.
Proof.
  intros n.
  induction n as [| n' H ].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.


Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l.
  induction l as [| h t H ].
  - reflexivity.
  - simpl.
    rewrite -> eqn_refl.
    rewrite -> H.
    reflexivity.
Qed.
















Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => eqb i j
  | _, _ => false
  end.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => leb i j
  | O, S _ => true
  | _, _ => false
  end.

Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | O, S_ => true
  | S i, S j => ltb i j
  | _, _ => false
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.



Lemma tst : forall (n : nat) (s : bag),
  count n (n :: s) = S (count n s).
Proof.
  intros n s.
  simpl.
  rewrite -> eqn_refl.
  reflexivity.
Qed.

Lemma leb_n_Sn : forall (n : nat), (n <=? S n) = true.
Proof.
  intros n.
  simpl.
  induction n as [| n' H].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Lemma leb_1_Sn : forall (n : nat), (1 <=? S n) = true.
Proof.
  intros n.
  simpl.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s.
  rewrite -> tst.
  rewrite -> leb_1_Sn .
  reflexivity.
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s.
  induction s as [| h t H ].
  - simpl.
    reflexivity.
  - destruct h as [| h'].
    * simpl.
      rewrite -> leb_n_Sn.
      reflexivity.
    * simpl.
      rewrite -> H.
      reflexivity.
Qed.

Theorem count_sum_distr: forall (n : nat) (s1 s2: bag),
  count n (sum s1 s2) = count n s1 + count n s2.
Proof.
  intros n s1 s2.
  induction s1 as [| h t H ].
  - reflexivity.
  - simpl.
    destruct (eqn h n) as [|].
    * simpl.
      rewrite -> H.
      reflexivity.
    * simpl.
      rewrite -> H.
      reflexivity.
Qed.

Search (?l = ?m -> rev ?l = rev ?m).

Lemma rev_injective_reverse: forall (l m : natlist), l = m -> rev l = rev m.
Proof.
  intros l m H.
  rewrite -> H.
  reflexivity.
Qed.

Search (rev [] = []).
Search (rev (rev ?l) = ?l).

Lemma rev_nil: forall (l : natlist), rev l = [] -> l = [].
Proof.
  intros l H.
  assert (G: rev (rev l) = rev []). {
    rewrite -> (rev_injective_reverse (rev l) [] H).
    reflexivity.
  }
  rewrite <- test_rev2.
  rewrite <- G.
  rewrite -> rev_involutive.
  reflexivity.
Qed.


Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  assert (G : rev (rev l1) = l1). {
    rewrite -> rev_involutive.
    reflexivity.
  }
  rewrite <- G.
  rewrite -> H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.











Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.


Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l as [| h t].
  - reflexivity.
  - simpl.
    reflexivity.
Qed.

End NatList.



Module PartialMap.
Export NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  intros x.
  destruct x as [n].
  simpl.
  induction n as [| n' H ].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq : forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.
  rewrite -> eqb_id_refl.
  reflexivity.
Qed.

Theorem update_neq : forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

End PartialMap.
