From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* 2.1.1 *)
CoInductive MyUnit: Type := MkMyUnit: MyUnit.
Definition pairNP: nat * Prop := (0, MyUnit).
Fail Definition pairNT: nat * Type := (0, MyUnit). (* Why? *)

(* exist and *)
Goal forall A (B: A -> Prop),
  (exists (x: A), B x) <-> (forall C: Prop, (forall x, B x-> C) -> C).
  move => A B; split.
  - move => [x bx C H]. apply (H x bx).
  move => H.
  apply (H (exists x, B x)) => x bx.
  exists x; apply bx.
Qed.
