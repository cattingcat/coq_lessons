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

  