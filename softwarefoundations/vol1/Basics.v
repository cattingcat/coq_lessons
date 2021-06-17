Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Definition deduct_types d := 
  match d with
  | monday => friday
  | _ => monday
  end.


Compute (deduct_types).
Compute (next_weekday tuesday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

From Coq Require Export String.



Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with 
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with 
  | false => false
  | true => b2
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with 
  | true => true
  | false => b2
  end.


Compute (negb true).
Compute (andb true true).
Compute (orb true false).


Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.



Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.



Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.






(* Ex 1 *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => 
    match b2 with
    | false => true
    | true => false
    end
  end.



Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.




(* Ex 2 *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := b1 && b2 && b3.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.






Check true.
Check negb.
Check bool.
Check Type.
(* Check "". *)
Check String.










Inductive rgb : Type := 
  | red
  | green
  | blue.

Inductive color : Type :=
  | white
  | black
  | other (c : rgb).


Definition is_mono (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | other _ => false
  end.

Definition is_red (c : color) : bool := 
  match c with
  | other red => true
  | _ => false
  end.






Module TestMod.
  Inductive color : Type :=
    | w
    | b
    | o (c : rgb).
End TestMod.


Check TestMod.color.
Check color.



Module TuplePlayground.

Inductive bit : Type := B0 | B1.

Inductive nybble : Type := bits (b0 b1 b2 b3 : bit).

Check (bits B0 B1 B1 B0) : nybble.

Definition all_zeros (n : nybble) : bool :=
  match n with 
  | bits B0 B0 B0 B0 => true
  | _ => false
  end.

Compute (all_zeros (bits B0 B0 B0 B1)).
Compute (all_zeros (bits B0 B0 B0 B0)).

End TuplePlayground.



Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).


Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.

Check (pred (S (S (S O)))).

Fixpoint even (n : nat) : bool :=
  match n with 
  | O => true
  | S O => false
  | S (S m) => even m
  end.

Compute (even (S (S (S O)))).
Compute (even (S (S (S (S O))))).


Definition odd (n : nat) := negb (even n).

Definition odd' : nat -> bool 
:= 
  fun n => negb (even n).


Fixpoint add (n : nat) (m : nat) : nat := 
  match n with
  | S i => add i (S m)
  | O => m
  end.

Fixpoint mul (n : nat) (m : nat) : nat :=
  match n with 
  | O => O
  | S i => add m (mul i m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n : nat) (m : nat) : nat :=
  match n, m with 
  | O, _ => O
  | i, O => i
  | S i, S j => minus i j 
  end.


Fixpoint exp (pow base : nat) : nat :=
  match pow with
  | O => S O
  | S i => mul base (exp i base)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with 
  | O => O
  | S O => S O
  | S i => mul n (factorial i)
  end.

Compute (factorial (S (S (S (S (S O)))))).



Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Example tst_minus_assoc: 
  ((S (S O)) - (S O) - (S O)) = (((S (S O)) - (S O)) - (S O)).

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



Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | O, S_ => true
  | S i, S j => ltb i j
  | _, _ => false
  end.


Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Compute ltb (S O) O.

(*
Example tstltb: 
  ltb (S O) O = false.
*)

End NatPlayground.






Check (S (S (S (S O)))).














