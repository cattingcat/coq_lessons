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
Qed.

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