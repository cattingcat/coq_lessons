From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Goal ~(forall X: Prop, X).
Proof.
  move => H.
  apply H.
Qed.