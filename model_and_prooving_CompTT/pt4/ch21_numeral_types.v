From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive numeral:  nat -> Type :=
  | Z: forall n, numeral n.+1
  | U: forall n, numeral n -> numeral n.+1.

Print numeral_ind.

Definition numeral_ind2 
  (P : forall n : nat, numeral n -> Prop)
  (fz : forall n : nat, P n.+1 (Z n))
  (fu : forall (n : nat) (n' : numeral n), P n n' -> P n.+1 (U n'))
  := 
    fix F (n: nat) (n': numeral n) {struct n'} : P n n' :=  
      match n' as n2 in (numeral n1) return (P n1 n2) with
      | Z n1 => fz n1
      | @U n1 n2 => fu n1 n2 (F n1 n2)
      end.


Definition P: forall n, numeral n.+1 -> option (numeral n) :=
  fun n num =>
    match num with
    | Z n' => None
    | U _ n' => Some n'
    end.

Print Empty_set.
Print void.
Definition P': forall n, numeral n -> match n with
                                      | 0 => void
                                      | S n' => option (numeral n')
                                      end :=
  fun _ num =>
    match num with
    | Z n' => None
    | U _ n' => Some n'
    end.

Definition P2: forall n, numeral n.+1 -> option (numeral n) := 
  fun n num => @P' n.+1 num.

Definition P'': forall n, numeral n.+2 -> numeral n.+1 :=
  fun n num => 
    match @P' n.+2 num with
    | Some a => a
    | None => Z n
    end.

(* 21.2.1 *)
Lemma constr_disj: forall n (a: numeral n), @Z n <> @U n a.
Proof.
  by move => n a H.
Qed.
Print constr_disj.

(* 21.2.2 *)
Lemma num0: numeral 0 -> void.
Proof.
  by apply P'.
Qed.

(* 21.2.3 *)
Definition num_listing: forall (n: nat), seq (numeral n) :=
  fix F n :=
    match n with 
    | 0 => [::]
    | n'.+1 => [:: Z n' & map (@U n') (F n')]
    end.

Compute num_listing 6.


(* 21.3 Inversion *)
Definition num_inv: forall {n} (a: numeral n),
  match n return numeral n -> Type with
  | 0 => fun _ => void
  | S n' => fun a => sum (a = Z n') { a' & a = U a' }
  end a.
Proof.
  move => n.
  case => [a | n' a].
  - by left.
  right.
  by exists a.
Defined.
(* ^ see chipala convoy pattern *)

Eval cbn in fun n => num_inv (Z n).
Eval cbn in fun n (a: numeral n) => num_inv (U a).



Theorem inversion: forall n (a: numeral n.+1),
  { a' & a = @U n a' } + { a = Z n }.
Proof.
  move => n a.
  case (@num_inv n.+1 a).
  - by right.
  by left.
Defined.

(* 21.3.1 *)

Lemma U_inj: forall n a b, @U n a = @U n b -> a = b.
Proof.
  move => n a b H.
  move: ((@f_equal _ _ (@P n) (@U n a) (@U n b)) H).
  rewrite /P.
  by case.
Qed.
  

Definition dec (X: Type) := sum X (X -> False).
Lemma numeral_decidable:
  forall n (a b: numeral n), dec (a = b).
Proof.
  move => n.
  elim => [n' b | n' b IH b'].
  - case (@inversion n' b).
      move => [a' Hb].
      right.
      by rewrite Hb.
    move => ->.
    by left.
  case (@inversion n' b').
    move => [a' ->].
    case (IH a').
      move => ->.
      by left.
    move => contra.
    right => H.
    apply contra.
    by apply (U_inj H).
  move => ->.
  by right.
Qed.

(* 21.3.2 *)
(* TODO *)
  
(* 21.3.3 *)
(* TODO *)
  
(* 21.4 Embedding numerals to numbers *)
Definition to_nat: forall n, numeral n -> nat :=
  fix F n m :=
    match m with
    | Z _ => 0
    | U n' m' => S (F n' m')
    end.

Compute (to_nat (U (U (Z 3)))).

Lemma numeral_upper: forall n (a: numeral n), to_nat a < n.
Proof.
  move => n.
  elim => [n' //| n' a' IH].
  by rewrite /to_nat -/to_nat -addn1 -[n'.+1]addn1 ltn_add2r.
Qed.

Lemma to_nat_inj: forall n,
  injective (@to_nat n).
Proof.
  move => n.
  elim => [n' b // | n' a IH b].
    move: (inversion b) => [[b' -> Contra] | -> //].
    exfalso. move: Contra.
    by rewrite /to_nat -/to_nat.
  move: (inversion b) => [[b' ->] | -> //].
  rewrite /to_nat -/to_nat.
  by move /succn_inj /IH ->.
Qed.

Fixpoint from_nat k n : numeral n.+1 :=
  match k, n with
  | 0, m => Z m
  | (S k), 0 => Z 0
  | (S k), (S m) => U (from_nat k m)
  end.

Lemma from_nat_step: forall n m,
  from_nat m.+1 n.+1 = U (from_nat m n).
Proof.
  by [].
Qed.

Lemma form_to: forall n (a: numeral n.+1), from_nat (to_nat a) n = a.
Proof.
  move => n a.
  move: (inversion a) => [[a' ->] | -> //].
  elim a' => [n'| n' a''].
    by rewrite /to_nat -/to_nat /from_nat.
  by rewrite /to_nat -/to_nat from_nat_step => ->.
Qed.

Lemma to_from: forall k n, k <= n -> @to_nat n.+1 (from_nat k n) = k.
Proof.
  elim => [n Hl // | n IH k' Hl].
  rewrite /from_nat -/from_nat.
  case E: k'.
    exfalso. move: E Hl => ->.
    by rewrite ltn0.
  move: E Hl => ->.
  rewrite ltnS => Hl.
  move: (IH _ Hl).
  by rewrite {2}/to_nat -/to_nat => ->.
Qed.

(* 21.4.1 *)
Definition lift_numeral: forall n (a: numeral n), numeral n.+1 :=
  fix F n a :=
    match a with
    | Z n' => Z n'.+1
    | @U m k => @U m.+1 (F m k)
    end.

Lemma lift_numeral_inj: forall n,
  injective (@lift_numeral n).
Proof.
  move => n.
  elim => [n' b // |n' a IH b ].
    move: (inversion b) => [[a' ->] | -> //].
    rewrite /lift_numeral -/lift_numeral.
    move => contra. exfalso.
    by [].
  move: (inversion b) => [[a' ->] | -> //].
  by rewrite /lift_numeral -/lift_numeral => /U_inj /IH ->.
Qed.
  
(* 21.5 Recursive numeral types *)
Fixpoint finT (n: nat): Type :=
  match n with
  | 0 => void
  | n'.+1 => option (finT n')
  end.

(* 21.5.1 *)
Definition num_fin: forall n (a: numeral n), finT n := 
  fix F n a :=
    match a with
    | Z _ => None
    | U n' a => Some (F n' a)
    end.

Fixpoint fin_num {n} (a: finT n): numeral n :=
  match n, a with
  | 0, c => match c with end
  | S n', None => Z n'
  | S n', Some a' => U (fin_num a')
  end.

(* 21.5.2 *)
Lemma finT0: finT 0 -> False.
Proof.
  by case.
Qed.

Lemma finT_inversion: forall n (a: finT n.+1), 
  sum (a = None) { a' & a = Some a' }.
Proof.
  move => n.
  elim.
Admitted. (*Defined.*)

(* TODO: custom eliminator *)