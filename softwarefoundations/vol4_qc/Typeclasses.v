From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Require Import List. Import ListNotations.
Local Open Scope string.


Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".


Class Show A : Type :=
  {
    show : A -> string
  }.

Instance showBool : Show bool :=
  {
    show := fun (b: bool) => if b then "true" else "false"
  }.

Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.

Search (string -> string -> string).
Instance showBoolNatPair : Show (bool * nat) :=
  {
    show := fun '(b, n) => "(" ++ (show b) ++ ", " ++ (show n) ++ ")"
  }.

Compute (show 42).

Compute (show (true, 42)).


Definition showOne {A : Type} `{Show A} (a : A) : string :=
  "The value is " ++ show a.


Class Eq A :=
{
  eqb: A -> A -> bool;
}.
Notation "x =? y" := (eqb x y) (at level 70).

Instance eqBool : Eq bool :=
  {
    eqb := fun (b c : bool) =>
       match b, c with
         | true, true => true
         | true, false => false
         | false, true => false
         | false, false => true
       end
  }.

Instance eqNat : Eq nat :=
  {
    eqb := Nat.eqb
  }.

Instance eqBoolFoolFunc : Eq (bool -> bool) :=
  {
    eqb := fun (f1 f2: bool -> bool) => 
      match f1 true =? f2 true, f1 false =? f2 false with
      | true, true => true
      | _, _ => false
      end
  }.



Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {
    show p :=
      let (a,b) := p in "(" ++ show a ++ "," ++ show b ++ ")"
  }.

Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
  {
    eqb p1 p2 :=
      let (p1a,p1b) := p1 in
      let (p2a,p2b) := p2 in
      andb (p1a =? p2a) (p1b =? p2b)
  }.

Fixpoint showListAux {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil         => ""
    | cons h nil  => s h
    | cons h t    => append (append (s h) ", ") (showListAux s t)
  end.
Instance showList {A : Type} `{Show A} : Show (list A) :=
  {
    show l := append "[" (append (showListAux show l) "]")
  }.

Fixpoint eqListAux {A: Type} `{Eq A} (l1 l2: list A): bool :=
  match l1, l2 with
  | nil, nil => true
  | h :: t, h' :: t' => andb (h =? h') (eqListAux t t')
  | _, _ => false
  end.
Instance eqList {A : Type} `{Eq A} : Eq (list A) :=
  {
    eqb := eqListAux
  }.

Print option.

Instance showOption {A: Type} `{Show A} : Show (option A) :=
  {
    show p := match p with
              | Some a => "Some " ++ show a
              | None => "None"
              end
  }.

Instance eqOption {A: Type} `{Eq A} : Eq (option A) :=
  {
    eqb p1 p2 :=  match p1, p2 with
                  | Some a, Some b => a =? b
                  | None, None => true
                  | _, _ => false
                  end
  }.

Instance eqBoolAFunc {A: Type} `{Eq A}: Eq (bool -> A) :=
  {
    eqb := fun (f1 f2: bool -> A) => 
      match f1 true =? f2 true, f1 false =? f2 false with
      | true, true => true
      | _, _ => false
      end
  }.

Compute ((fun (a b: bool) => 41 + 1) =? (fun (a b: bool) => 42)).



Class Ord A `{Eq A} : Type :=
  {
    le : A -> A -> bool
  }.
Check Ord.


Instance natOrd : Ord nat :=
  {
    le := Nat.leb
  }.

Definition max {A: Type} `{Ord A} (x y : A) : A :=
  if le x y then y else x.


Instance pairOrd {A B: Type} `{Ord A} `{Ord B} : Ord (A * B) :=
  {
    le p1 p2 := 
      let (a, b) := p1 in
      let (a', b') := p2 in
        if a =? a' then le b b' else le a a'
  }.

Instance optionOrd {A: Type} `{Ord A} : Ord (option A) :=
  {
    le p1 p2 := match p1, p2 with
                | Some a, Some b => le a b
                | Some _, None => false
                | None, None => true
                | None, Some _ => true
                end
  }.

Fixpoint listOrdAux {A: Type} `{Ord A} (p1 p2: list A) :=
  match p1, p2 with
  | h :: t, h' :: t' => if h =? h' then listOrdAux t t' else le h h'
  | _ :: _, nil => false
  | nil, nil => true
  | nil, _ => true
  end.

Instance listOrd {A: Type} `{Ord A} : Ord (list A) :=
  {
    le := listOrdAux
  }.

Definition showOne3 {A: Type} `{H : Show A} (a : A) : string :=
  "The value is " ++ show a.




