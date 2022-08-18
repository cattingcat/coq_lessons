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
Lemma enc0: forall c, encode c = 0 -> c = (0, 0).
Proof.
  move => [x y].
  case x; case y => //.
Qed.

Lemma step_enc: forall x y, next (S x, y) = (x, S y).
Proof. by []. Qed.

Lemma step_enc': forall x, next (0, x) = (S x, 0).
Proof. by []. Qed.

Theorem eq': forall c, decode (encode c) = c.
Proof.
  move => c.
  (* elim: {-1}(encode c) (erefl (encode c)). *)
  have H: (forall ec, encode c = ec -> decode ec = c) -> (decode (encode c) = c).
    move => Hec.
    by apply Hec.
  apply H => {H}.
  move => ec.
  move: c.
  elim: ec => [c |n IH c].
    by move/enc0 ->.
  rewrite /decode -/decode.
  case: c IH => [x y] IH.
  case x; case y => //.
    move => n'.
    rewrite -step_enc step => H.
    rewrite (IH (1, n')) => //.
    by apply (eq_add_S _ _ H).

    move => n'.
    rewrite -step_enc' step => H.
    rewrite (IH (0, n')) => //.
    by apply (eq_add_S _ _ H).

    move => n' n''.
    rewrite -step_enc step => H.
    rewrite (IH (n''.+2, n')) => //.
    by apply (eq_add_S _ _ H).
Qed.

(* 7.2.4 *)

Section tst.
Variables x y: nat.
Goal x = y -> x == y.
Proof.
  move/eqnP. (* reflection between = and eqn *)
  Print eqnP.
  Search (eqn _ _ = _ == _).
  Print erefl.
  rewrite {1}eqnE. (* equality betweek eqn and == *)
  by [].
Qed.
End tst.