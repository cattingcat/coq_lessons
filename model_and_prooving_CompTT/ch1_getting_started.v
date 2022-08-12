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

(* Ex 1.5.1 *)
Definition D x y := (x - y) + (y - x).

Lemma Dsymm: forall x y, D x y = D y x.
Proof.
  elim => [y | y IH x'].
  - unfold D.
    rewrite minus_0 sub0n addition_comm //.
  unfold D in *.
  case x'.
  - rewrite minus_0 sub0n addition_comm //.
  move => k.
  by rewrite subSS subSS IH.
Qed.


(* Ex 1.5.2 *)
Fixpoint M x y := 
  match x, y with
  | S x', S y' => S(M x' y')
  | S _, _ => x
  | _ , S _ => y
  | _, _ => x
  end.

Lemma mSS: forall x y, M (S x) (S y) = S (M x y).
Proof.
  by move => x y.
Qed.

Lemma mXX: forall x, M x x = x.
Proof.
  elim => [//| n' IH].
  by rewrite mSS IH.
Qed.

Lemma mX0: forall x, M x 0 = x.
Proof.
  by case.
Qed.

Lemma M_comm: forall x y, M x y = M y x.
Proof.
  elim => [y| n IH y].
    case y.
      done.
    by move => n.
  case y.
    done.
  move => n'.
  by rewrite mSS mSS IH.
Qed.

Lemma M_dom: forall x y, M (x + y) y = x + y.
Proof.
  move => x y.
  elim: y x => [x| y' IH x].
    by rewrite addn0 mX0.
  by rewrite addnS mSS IH.
Qed.
  
(* Ex 1.5.3 *)
Fixpoint add_symm (x: nat) (y: nat) :=
  match x, y with 
  | 0, 0 => 0
  | 0, S y' => S y'
  | S x', 0 => S x'
  | S x', S y' => S (S (add_symm x' y'))
  end.

Lemma addSymS0: forall x, add_symm (S x) 0 = S x.
Proof. by done. Qed.

Lemma addSymSS: forall x y, add_symm (S x) (S y) = S (S (add_symm x y)).
Proof. by done. Qed.

Lemma add_symm_comm: forall x y, add_symm x y = add_symm y x.
Proof.
  elim => [y| x IH y].
    by case y.
  case y.
    by done.
  move => y'.
  by rewrite addSymSS addSymSS IH.
Qed.

Lemma add_symm_0n: forall x, add_symm 0 x = x.
Proof.
  by case.
Qed.

Lemma add_symm_Sn: forall x y, add_symm (S x) y = S (add_symm y x).
Proof.
  move => x y.
  elim: y x => [x| n IH ].
    rewrite addSymS0.
    by case x.
  move => x.
  rewrite addSymSS.
  case: x.
    by rewrite add_symm_0n.
  move => n'.
  by rewrite IH addSymSS.
Qed.

Lemma add_symm_add_equiv: forall x y, add_symm x y = x + y.
Proof.
  elim => [y|x IH y'].
    by rewrite add_symm_0n.
  case y' => [|y''].
    by rewrite addSymS0 addn0.
  by rewrite addSymSS IH addSn addnS.
Qed.


(* Ex 1.6 *)