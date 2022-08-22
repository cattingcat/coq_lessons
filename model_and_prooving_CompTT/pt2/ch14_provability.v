From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition provable (P: Prop) := P -> P.

Definition disprovable (P: Prop) := provable (~P).
Definition consistent (P: Prop) := ~ provable (~P).
Definition independent (P: Prop) := (~ provable P) /\ ~ (provable (~ P)).

