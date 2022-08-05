From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Ex 1.2.1 *)
Fixpoint min (a: nat) (b: nat) : nat := 
  match a, b with
  | S a', S b' => S (min a' b')
  | _, _ => O
  end.

Compute (min 7 5).
Search true.

Fixpoint is_eq (a: nat) (b: nat) : bool := 
  match a, b with
  | O, O => true
  | S a', S b' => is_eq a' b'
  | _, _ => false
  end.

Fixpoint is_less (a: nat) (b: nat) : bool :=
  match a, b with
  | S a', S b' => is_less a' b'
  | O, S _     => true
  | _, _       => false
  end.

Search (bool -> bool -> bool).

Lemma tst: forall y, true && y = y /\ false && y = false.
Proof.  
  move => y.
  case: y.
  - done.
  done. 
Qed.
  (* set t := true && y.    -- new variable introduction *)

Lemma plus_zero: forall x, x + 0 = x.
Proof.
  elim => [| n IH].
  - done.
  Search (_.+1 + _).
  by rewrite addSn IH.
Qed.
  
Lemma plus_sx: forall x y, x + y.+1 = (x + y).+1.
Proof.
  move => x y.
  elim: x y => [ x | x IH y'] //.
  - by rewrite addSn addSn IH. 
Qed.

Lemma addition_comm: forall x y, x + y = y + x.
Proof.
  elim => [y|y IH y']. rewrite plus_zero //.
  rewrite plus_sx -IH //.
Qed.


Lemma ind_test: forall x y, x + y - y = x.
Proof.
  move => x.
  elim => [| n IH].
  - rewrite plus_zero.
    case x.
    -- done.
    -- done.
  - rewrite  plus_sx.
    Search (_.+1 - _.+1).
    rewrite subSS.
    apply IH.
Qed.

Lemma add_assoc: forall x y z, (x + y) + z = x + (y + z).
Proof.
  elim => [y z //| x IH y z].
  rewrite (addition_comm x.+1 y) plus_sx addition_comm plus_sx.
  rewrite (addition_comm x.+1 (y + z)) plus_sx addition_comm (addition_comm y x).
  rewrite (addition_comm (y + z) x) IH //.
Qed.

Lemma add_distr: forall x y z, (x + y) * z = x * z + y * z.
Proof.
  elim => [x y|x IH y z].
  rewrite addition_comm plus_zero //.
  rewrite addition_comm plus_sx.
  Search (_.+1 * _).
  rewrite mulSn mulSn (add_assoc) -IH (addition_comm x y) //.
Qed.

Lemma mul_comm: forall x y, x * y = y * x.
Proof. Admitted.

Lemma minus_0: forall x, x - 0 = x.
Proof.
  elim => [//| x IH].
  done.
Qed.

Lemma minus_sum: forall x y, x - (x + y) = 0.
Proof.
  elim => [y | x IH y].
  rewrite addition_comm plus_zero //.
  rewrite addition_comm plus_sx addition_comm subSS IH //.
Qed.

Lemma sub_aa: forall x, x - x = 0.
Proof.
  elim => [//| x IH].
  rewrite subSS IH //.
Qed.

Lemma sum_sub: forall x y, x + y - x = y.
Proof.
  elim => [ y |y IH y'].
  rewrite addition_comm plus_zero minus_0 //.
  rewrite addition_comm plus_sx subSS addition_comm //.
Qed.