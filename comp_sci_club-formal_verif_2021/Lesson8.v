From mathcomp Require Import all_ssreflect.

Module Lesson8.
(* Canonical structures *)

Structure myType := Pack {
  sort: Type;
  to_nat_op: sort -> nat;
  spec : forall x y, x = y -> to_nat_op x = to_nat_op y;
}.

(* myType - Type, Pack - ctor *)
(* Structure - inductive type with generated accessors*)
Check myType.
Check Pack.
Check to_nat_op.

Coercion sort: myType >-> Sortclass. (* Sortclass - Type or Prop *)

Definition nat_myType_op: nat -> nat := (fun n => n.+1).
Lemma nat_myType_spec: forall x y, x = y -> nat_myType_op x = nat_myType_op y.
Proof.
move=> x y eq_xy. by rewrite /nat_myType_op eq_xy.
Qed.

Canonical myType_nat := Pack nat nat_myType_op nat_myType_spec.

Print Canonical Projections.


Definition myFunc {T: myType} (a b: T) : nat :=
  to_nat_op _ a + to_nat_op _ b.

Compute myFunc 1 1.


Definition pair_nat_op {A B: myType}: (A * B) -> nat :=
  fun '(a, b) => to_nat_op _ a + to_nat_op _ b.
Lemma pair_nat_myType_spec {A B: myType}: forall (x y: (A * B)), 
  x = y -> pair_nat_op x = pair_nat_op y.
Proof.
move=> x y eq_xy. by rewrite eq_xy.
Qed.

Canonical myType_pair_nat (A B: myType) := Pack (A * B) pair_nat_op pair_nat_myType_spec.

Compute myFunc (1, 2) (3, 4).


(* Canonical structures - 1 type - 1 definition (coherent) *)
(* Typeclasses          - 1 type - many instances (not coherent) *)


Print Monoid.law.


End Lesson8.
