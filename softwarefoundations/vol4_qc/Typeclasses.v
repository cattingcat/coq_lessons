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


Class Show (A : Type) :=
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

Definition maxOrEq {A: Type} `{Ord A} (x y : A) : A :=
  if le x y 
    then 
      if x =? y then x else y
    else x.


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



 Record Point :=
  MkPoint
    {
      px : nat;
      py : nat
    }.

Check (MkPoint 2 4).
Check {| px := 2; py := 4 |}.
Check {| py := 4; px := 2 |}.

Definition r : Point := {| px := 2; py := 4 |}.
Compute (r.(px) + r.(py)).

Record LabeledPoint (A : Type) :=
  Build_LabeledPoint
    {
      lx : nat;
      ly : nat;
      label : A
    }.

Check {| lx:=2; ly:=4; label:="hello" |}.


Print Show.
Print showNat.
Print HintDb typeclass_instances.

Set Typeclasses Debug.
Check (show 42).
Check (show (true,42)).
Unset Typeclasses Debug.



From Coq Require Import Relations.Relation_Definitions.

Class Reflexive (A : Type) (R : relation A) :=
  {
    reflexivity : forall x, R x x
  }.

Class Transitive (A : Type) (R : relation A) :=
  {
    transitivity : forall x y z, R x y -> R y z -> R x z
  }.


Lemma trans3 : forall {A R} `{Transitive A R} x y z w,
    R x y -> R y z -> R z w -> R x w.
Proof.
  intros.
  apply (transitivity x z w). apply (transitivity x y z).
  assumption. assumption. assumption. Defined.

Class PreOrder (A : Type) (R : relation A) :=
  { PreOrder_Reflexive :> Reflexive A R ;
    PreOrder_Transitive :> Transitive A R }.

Lemma trans3_pre : forall {A R} `{PreOrder A R} x y z w,
    R x y -> R y z -> R z w -> R x w.
Proof. intros. eapply trans3; eassumption. Defined.

Print PreOrder.



Require Import ssreflect ssrbool.
Print decidable.

Class Dec (P : Prop) : Type :=
  {
    dec : decidable P
  }.

Class EqDec (A : Type) {H : Eq A} :=
  {
    eqb_eq : forall x y, x =? y = true <-> x = y
  }.

Instance EqDec__Dec {A} `{H : EqDec A} (x y : A) : Dec (x = y).
Proof.
  constructor.
  unfold decidable.
  destruct (x =? y) eqn:E.
  - left. rewrite <- eqb_eq. assumption.
  - right. intros C. rewrite <- eqb_eq in C. rewrite E in C. inversion C.
Defined.

Instance Dec_conj {P Q} {H : Dec P} {I : Dec Q} : Dec (P /\ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; auto;
      right; intro; destruct H; contradiction.
Defined.
