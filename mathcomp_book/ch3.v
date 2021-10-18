From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Print eq.

Set Printing Universes.
Check Type: Type.
Check Prop: Type.


Section tst.
Variable t : nat -> Type.
Variable g : forall n, t n.

End tst.



Inductive my_type := A (i: nat) | B (j: bool).

Definition tst: my_type -> bool :=
  fun t => match t with
           | A i => true
           | B i => false
           end.

Compute (tst (A 1)).
Compute (tst (B false)).

Definition coerce_bool_pred: bool -> Prop :=
  fun b => b = true.

Coercion coerce_bool_pred: bool >-> Sortclass.