From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Theorem leibniz_symm: forall (X : Type) (x y : X), 
  (forall (p: X -> Prop), p x -> p y) -> (forall (p: X -> Prop), p y -> p x).
Proof.
  move => X x y H p py.
  set H' := H (fun z => p z -> p x).
  move: H'; rewrite /H; apply.
    by [].
  by apply py.
Qed.

Lemma tst: forall Z: Type, False -> Z.
Proof.
  move => F f.
  case f.
Defined.

(* 4.3.1 *)
Inductive FalseInd : Prop := C (f: FalseInd).
Fixpoint elim_false (Z: Type) (f: FalseInd): Z :=
  match f with 
  | C f' => elim_false Z f'
  end.