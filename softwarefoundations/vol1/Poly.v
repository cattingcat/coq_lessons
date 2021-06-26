Module Poly.
From LF Require Export Lists.
From LF Require Export Basics1.
From LF Require Export Induction.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list.
Check nil.
Check cons.
Check (cons nat 3 (nil nat)) : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

(* make type param implicit *)
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.


Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 : rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2: rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


(* explicit type arg *)
Check @nil : forall X : Type, list X.



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




Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y): list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | cons (x,y) t =>
    match split t with
    | (lx, ly) => (x::lx, y::ly)
    end
  end.


Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.







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
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | cons h t => Some h
  end.


Check @hd_error : forall X : Type, list X -> option X.
Check hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.







Definition doit3times {X : Type} (f : X -> X) (n : X) : X := f (f (f n)).


Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Fixpoint filter {X: Type} (test: X -> bool) (l: list X) : list X :=
  match l with
  | []     => []
  | h :: t =>
    if test h 
    then h :: (filter test t)
    else filter test t
  end.

(*
Definition countoddmembers' (l: list nat) : nat := length (filter odd l).
*)

Example test_anon_fun': doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.


Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun i => andb (negb (Induction.leb i 7)) (Induction.even i)) l.


Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.


Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter (fun i => test i) l, filter (fun i => negb (test i)) l).


Example test_partition1: partition (fun i => negb (Induction.even i)) [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.


Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.


Lemma map_dist : forall (X Y : Type) (f : X -> Y) (l m : list X),
  map f (l ++ m) = map f l ++ map f m.
Proof.
  intros X Y f l m.
  induction l as [| h t H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| h t H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> map_dist.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.


Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X): list Y :=
  match l with 
  | nil => nil
  | cons h t => f h ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X): option Y :=
  match xo with
  | None   => None
  | Some x => Some (f x)
  end.




Fixpoint map' (X Y : Type) (f : X -> Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map' X Y f t)
  end.

Fixpoint filter' (X: Type) (test: X -> bool) (l: list X) : list X :=
  match l with
  | []     => []
  | h :: t =>
    if test h 
    then h :: (filter' X test t)
    else filter test t
  end.




Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y): Y :=
  match l with
  | nil    => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.
Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.
Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.


Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [| h t H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- H.
    reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun i a => [f i] ++ a ) l [].

Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [| h t H ].
  - reflexivity.
  - simpl.
    rewrite <- H.
    reflexivity.
Qed.




Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with
  | (x, y) => f x y
  end.

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.


Check @prod_curry.
Check @prod_uncurry.
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  unfold prod_uncurry.
  unfold prod_curry.
  reflexivity.
Qed.


Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  unfold prod_uncurry.
  unfold prod_curry.
  simpl.
  destruct p as [x y].
  - reflexivity.
Qed.

Fixpoint nth_error' {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | []      => None
  | a :: l' => if n =? O then Some a else nth_error' l' (pred n)
  end.

Lemma len_0_for_empty: forall {X : Type} (l : list X), length l = 0 -> l = nil.
Proof.
  intros X l.
  induction l as [| h t H ].
  - reflexivity.
  - simpl.
Admitted.
  


Theorem tst : forall X l n, length l = n -> @nth_error X l n = None.
Proof.
  intros X l n H.
Admitted.



Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one  : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two  : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.



Definition succ (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).
  
Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.


Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.


Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition mult' (X : Type) (n m : (X -> X) -> X -> X) (f : X -> X) (x : X) := n (m f) x.

Definition exp (n m : cnat) : cnat := 
  fun (X : Type) (f : X -> X) (x : X) => (m _ (mult' X (n X)) (one X)) f x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.

End Poly.
