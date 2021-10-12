Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.

Check Nat.lt.
Check Nat.ltb.

Print reflect.
Check ltb_reflect.

Goal (3 <? 7 = true). Proof. reflexivity. Qed.


Theorem three_less_seven_1: 3 < 7.
Proof.
  assert (H := ltb_reflect 3 7).
  remember (3 <? 7) as b.
  destruct H as [P|Q] eqn:?.
  - (* Case 1: H = ReflectT (3<7) P *)
    apply P.
  - (* Case 2: H = ReflectF (3<7) Q *)
    compute in Heqb.
    inversion Heqb.
Qed.

Theorem three_less_seven_2: 3 < 7.
Proof.
  assert (H := ltb_reflect 3 7).
  inversion H as [P|Q].
  apply P.
Qed.


Module ScratchPad.

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B
 | right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Definition t4 := forall a b, {a < b} + {~(a < b)}.

Definition lt_dec (a: nat) (b: nat) : {a < b} + {~(a < b)} :=
  match ltb_reflect a b with
  | ReflectT _ P => left (a < b) (~ a < b) P
  | ReflectF _ Q => right (a < b) (~ a < b) Q
  end.

Definition lt_dec' (a: nat) (b: nat) : {a < b} + {~(a < b)}.
Proof.
  destruct (ltb_reflect a b) as [P|Q]. left. apply P. right. apply Q.
Defined.

Print lt_dec.
Print lt_dec'.

Theorem lt_dec_equivalent: forall a b, lt_dec a b = lt_dec' a b.
Proof.
  intros.
  unfold lt_dec, lt_dec'.
  reflexivity.
Qed.

End ScratchPad.


(* sumbool in the Coq Standard Library *)
Module ScratchPad2.
Locate sumbool. (* Coq.Init.Specif.sumbool *)
Print sumbool.

Definition lt_dec (a: nat) (b: nat) : {a < b} + {~(a < b)} :=
  match ltb_reflect a b with
  | ReflectT _ P => left P
  | ReflectF _ Q => right Q
  end.

Definition le_dec (a: nat) (b: nat) : {a <= b} + {~(a <= b)} :=
  match leb_reflect a b with
  | ReflectT _ P => left P
  | ReflectF _ Q => right Q
  end.

Fixpoint insert (x: nat) (l: list nat) :=
  match l with
  | nil  => x :: nil
  | h::t => if le_dec x h then x :: h :: t else h :: insert x t
  end.

Fixpoint sort (l: list nat) : list nat :=
  match l with
  | nil  => nil
  | h::t => insert h (sort t)
  end.

Inductive sorted: list nat -> Prop :=
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
   x <= y -> sorted (y::l) -> sorted (x::y::l).

Lemma insert_sorted: forall a l, 
  sorted l -> sorted (insert a l).
Proof.
  intros a l H.
  induction H.
  - constructor.
  - unfold insert.
    destruct (le_dec a x) as [ Hle | Hgt].
    + constructor; try assumption.
      constructor.
    + constructor.
      * lia.
      * constructor.
  - unfold insert.
    destruct (le_dec a x) as [ Hle | Hgt].
    + constructor; try assumption.
      constructor; try assumption.
    + fold insert.
      unfold insert in IHsorted.
      destruct (le_dec a y) as [ Hle' | Hgt'].
      * constructor; try assumption.
        lia.
      * fold insert in IHsorted.
        constructor; try assumption.
Qed.


Print or. (* Is a Prop *)
Print sumbool. (* Is a Set*)


Axiom lt_dec_axiom_1: forall i j: nat, 
  i < j  \/  ~(i < j).
(* Impossible to use Prop in Sets *)
Fail Definition max (i j: nat) : nat :=
   if lt_dec_axiom_1 i j then j else i.




Axiom lt_dec_axiom_2: forall i j: nat, 
  {i < j} + {~(i < j)}.
Definition max_with_axiom (i j: nat) : nat :=
   if lt_dec_axiom_2 i j then j else i.


Lemma prove_with_max_axiom: max_with_axiom 3 7 = 7.
Proof.
  unfold max_with_axiom.
  try reflexivity.
  (* uncomment this line and try it: *)
  Fail unfold lt_dec_axiom_2.

  destruct (lt_dec_axiom_2 3 7).
  reflexivity.
  contradiction n. lia.
Qed.

End ScratchPad2.


Lemma compute_with_lt_dec: (if ScratchPad2.lt_dec 3 7 then 7 else 3) = 7.
Proof.
  compute.
  (*unfold ltb_reflect.*) (* opaque usage *)
Abort.

Lemma compute_with_StdLib_lt_dec: (if lt_dec 3 7 then 7 else 3) = 7.
Proof.
  compute.
  reflexivity.
Qed.


Search ({_} + {~_}).

Definition list_nat_in: forall (i: nat) (al: list nat), {In i al} + {~ In i al}.
Proof.
  intros.
  induction al.
  - right. intros Hcontra. simpl in *.
    assumption.
  - destruct (Nat.eq_dec i a).
    + left. simpl. left. symmetry. assumption.
    + destruct IHal as [?|?].
      * left. simpl. right. assumption.
      * right. simpl. intro Hcontra.
        destruct Hcontra; auto.
Defined.

Example in_4_pi: (if list_nat_in 4 [3;1;4;1;5;9;2;6] then true else false) = true.
Proof.  simpl. reflexivity. Qed.









