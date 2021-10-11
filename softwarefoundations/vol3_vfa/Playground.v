Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.

Inductive tstind : nat -> Type :=
  kek (i: nat): forall (n: nat), tstind n.

Definition foo (n: nat) : tstind n := kek 0 n.

Definition bar: bool -> Type -> Type -> Type := fun b tl tr =>
  match b with
  | true => tl
  | false => tr
  end.


Definition barty (Tl Tr: Prop) : Prop := exists (b: bool), if b then Tl else Tr.

Definition inl_mysum (Tl Tr: Prop) (l: Tl) : barty Tl Tr.
Proof.
  intros.
  unfold barty.
  exists true.
  apply l.
Defined.

Print inl_mysum.


Definition sumT A B := sigT (fun (b : bool) => if b then A else B).
Definition inl_sumT A B (a: A) := @existT bool (fun (b : bool) => if b then A else B) true a.

(*Definition  barty nat bool := inl_mysum bool bool true.*)

Print ex. (* Sigma type for Prop *)
Print sigT. (* Sigma for Type *)
Print sig.

Definition foo11 : bool -> Type :=
  fun b => match b with
           | true => nat
           | false => bool
           end.

Definition bar11 : forall (b: bool) (c: foo11 b), nat := fun _ _ => 11.

Compute (bar11 false true).
Fail Compute (bar11 false 111).

Inductive Fin : nat -> Type :=
| FinItem (i: nat) : forall n, i < n -> Fin n.

Definition correctItem: Fin 2.
Proof.
  apply (FinItem 1).
  lia.
Defined.

Definition idA : forall (A: Type), A -> A :=
  fun (A: Type) (a: A) => a.


Locate "exists".

Definition even_nat := {x : nat | Nat.Even x}.

Print even_nat.


Module SigSandbox.
  Inductive sig {A : Type} (P : A -> Prop) : Type :=
  | exist (x : A) : P x -> sig P.

  Notation "{ x : A | P }" := (sig A (fun x => P x)).

  Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro (x : A) : P x -> ex P.

  Definition proj1_sig {A : Type} {P : A -> Prop} (e : sig P) : A :=
    match e with
    | exist _ x _ => x
    end.

  Definition proj2_sig {A : Type} {P : A -> Prop} (e : sig P) : P (proj1_sig e) :=
    match e with
    | exist _ _ p => p
    end.

  Fail Definition proj1_ex {A : Type} {P : A -> Prop} (e : ex P) : A :=
    match e with
    | ex_intro _ x _ => x
    end.
End SigSandbox.

Lemma tst_tact: forall A B, A -> (A -> B) -> B.
Proof.
  intros.
  pose (pB := X0 X).
  pose proof (pB' := X0 X).
  exact pB.
Qed.

Lemma tst_tact2: forall A B, A -> (A -> B) -> B.
Proof.
  intros.
  refine (X0 _).
  exact X.
Qed.

Lemma tst_tact3: forall A B, A \/ B -> (A -> B) -> B.
Proof.
  intros.
  case H.
  - intros. refine (H0 _). exact H1.
  - intros. exact H1.
Qed.

Lemma tst_nat_comm: forall n m, n + m = m + n.
Proof.
  intros.
  elim n.
Admitted.

