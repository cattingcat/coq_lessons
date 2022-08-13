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
Fixpoint is_even (n: nat): bool :=
  match n with 
  | 0 => true
  | S 0 => false
  | S (S n') => is_even n'
  end.

Lemma is_even_SS: forall n, is_even (S (S n)) = is_even n.
Proof. by done. Qed.

Fixpoint is_even' (n: nat): bool :=
  match n with 
  | 0 => true
  | S n' => negb (is_even' n')
  end.

Lemma double_even: forall n, is_even (n * 2).
Proof.
  elim => [|n' IH].
    by done.
  by rewrite mulnC mulnS addSn addSn add0n mulnC is_even_SS IH.
Qed.



Fixpoint fib (n: nat): nat :=
  match n with
  | 0 => 0
  | S n' => 
    match n' with 
    | 0 => S 0
    | S n'' => fib n'' + fib n'
    end
  end.

Fixpoint fib'_helper (n: nat) (b: bool): nat :=
  match n, b with
  | 0, false => 0
  | 0, true => 1
  | S n', false => fib'_helper n' true
  | S n', true => fib'_helper n' false + fib'_helper n' true
  end.

Definition fib' (n: nat): nat := fib'_helper n false.

Lemma unfold_fib'Sn: forall n, fib' (S n) = fib'_helper n true.
Proof. by []. Qed.

Compute (fib' 10).
Compute (fib 10).

Lemma fib_equiv': forall n, fib n = fib' n.
Proof.
  elim => [| n' IH].
    by done.
  case: n' IH => [| n IH].
    by done.
  rewrite /(fib n.+2) -/(fib n) -/(fib (n.+1)).
  rewrite /(fib' n.+2) /(fib'_helper _ _) -/(fib'_helper n false) -/(fib'_helper n.+1 false).
  rewrite -/(fib' _) -/(fib' _) IH.
  have: forall k, fib n = fib' n -> fib n + k = fib' n + k.
    move => k H.
    apply/eqnP.
    rewrite eqnE. eqn_add2r.
    apply /eqnP.
    by apply H.
  move => G.
  apply G => {G}.
  case: n IH => [| n IH].
  by done.
Admitted.

Fixpoint nat_ind2 P (p0: P 0) (p1: P 1) (f: forall n, P n -> P n.+2) n: P n.
Proof. 
  case: n.
    apply p0.
  case.
    apply p1.
  move => n.
  apply f.
  apply (nat_ind2 P p0 p1 f).
Defined.


Lemma fib_equiv'': forall n, fib n = fib' n.
Proof.
  apply nat_ind2.
    done.
    done.
  move => n IH.
  rewrite /(fib n.+2) -/(fib n) -/(fib (n.+1)).
  rewrite /(fib' n.+2) /(fib'_helper n.+2 false).
  rewrite -/(fib'_helper n false) -/(fib' n).
  rewrite -/(fib'_helper n true) -unfold_fib'Sn IH.
Admitted.

(* Lemma fib_equiv: forall n, fib n = fib' n.
Proof.
  elim => [//|].
  move => n.
  rewrite /(fib _) /(fib _) => IH.
  rewrite IH.
  move : IH.
  rewrite /(fib' _) /(fib'_helper _) => IH. *)

Definition fib_f (n: nat) (n0: nat) (n1: nat) (nf: nat -> nat): nat :=
  match n with
  | 0 => n0
  | S n' => 
    match n' with 
    | 0 => n1
    | S n'' => nf n''
    end
  end.

Fixpoint fib'_f (n: nat) (b: bool) (n0: nat) (n1: nat) (nf: nat -> nat): nat :=
  match n, b with
  | 0, false => n0
  | 0, true => n1
  | S n', false => fib'_f n' true n0 n1 nf
  | S n', true => nf n'
  end.

Lemma fib_core_equiv: forall n n0 n1 nf nf', 
  (forall k, nf k = nf' k) -> fib_f n n0 n1 nf = fib'_f n false n0 n1 nf'.
Proof.
  case => [//| n n0 n1 nf nf' H].
  rewrite /(fib_f) /(fib'_f).
  case: n => [// | n].
  by rewrite H.
Qed.

Section tst.
  Variables P Q : bool -> Prop.
  Hypothesis P2Q : forall a b, P (a || b) -> Q a.

  Goal forall a, P (a || a) -> True.
    move=> a HPa. move: {HPa}(@P2Q _ _ HPa) => HQa. 
  Admitted.
  Goal forall a, P (a || a) -> True.
    move=> a HPa. move/P2Q: HPa => HQa.
  Admitted.
  Goal forall a, P (a || a) -> True.
    move=> a. move/P2Q=> HQa.
  Admitted.
End tst.

Section tst2.
  Variables P Q: bool -> Prop.
  Hypothesis PQequiv : forall a b, P (a || b) <-> Q a.
  
  Goal forall a b, P (a || b) -> True.
    move=> a b; move/PQequiv=> HQab.
  Admitted.
  Goal forall a, P ((~~ a) || a).
    move=> a. apply/PQequiv.
  Admitted.
End tst2.


Lemma fib_equiv: forall n, fib n = fib' n.
Proof.
  elim => [//| n IH].
  (* rewrite {1}[n]/(0 + n). Rewrite firs occurence of n to 0 + n *)
  rewrite /(fib) -/(fib_f ).
  Print ltnP.
  move: addSn.
Admitted.

(* 1.6.3 *)
Fixpoint h' (n: nat) (b: bool): nat :=
  match n, b with
  | 0, false => 0
  | 0, true => 1
  | S n', false => h' n' true
  | S n', true => S (h' n' false)
  end.