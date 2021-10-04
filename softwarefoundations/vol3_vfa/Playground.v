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

Locate "exists".
