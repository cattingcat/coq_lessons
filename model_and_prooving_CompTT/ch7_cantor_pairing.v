From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition next (p: nat * nat): nat * nat :=
  match p with 
  | (0, y) => (S y, 0)
  | (S x, y) => (x, S y)
  end.

Compute (next (0,0)).
Compute (next (1,0)).
Compute (next (0, 1)).
Compute (next (3, 3)).

Fixpoint decode (n: nat): nat * nat :=
  match n with
  | 0 => (0, 0)
  | S n' => next (decode n')
  end.

Fixpoint s (n: nat) := 
  match n with 
  | 0 => 0
  | S n' => n + s n'
  end.

Definition encode (p: nat * nat): nat :=
  let (x, y) := p in s (x + y) + y.

(* 7.2.1 *)
Theorem step: forall c, encode (next c) = S (encode c).
Proof.
  move => [x y].
  elim x.
    by rewrite /next /encode addn0 addn0 add0n /(s y.+1) -/s addSn addnC.
  move => n IH.
  by rewrite /next /encode addnS addSn addnS.
Qed.

(* 7.2.2 *)
Theorem eq: forall n, encode (decode n) = n.
Proof.
  elim => [//| n IH].
  by rewrite /decode -/decode step IH.
Qed.

(* 7.2.3 *)
Theorem eq': forall c, decode (encode c) = c.
Proof.
