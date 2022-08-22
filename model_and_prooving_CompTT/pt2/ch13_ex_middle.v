From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition excluded_middle := forall (P: Prop), P \/ ~P.

(* 13.1.1 *)
Definition double_neg := forall (P: Prop), ~(~ P) -> P.
Definition contraposition := forall (P Q: Prop), (~P -> ~Q) -> Q -> P.

Definition proof_by_contra: forall P, excluded_middle ->  (~P -> False) -> P.
Proof.
  move => P em contra.
  case (em P).
    done.
  move => np.
  exfalso.
  apply (contra np).
Qed.


(* 13.3 *)
Definition stable (P: Prop) := ~(~ P) -> P.

(* 13.4 *)
Definition definite (P: Prop) := P \/ ~P.