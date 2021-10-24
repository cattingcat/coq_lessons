From mathcomp
  Require Import ssreflect ssrbool ssrnat.

Lemma forallD A (P Q: A -> Prop):
  (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x).
Proof.
move=> H px x.
apply: (H x).
apply: px.
Qed.


Module Connectives.
Variables P Q R: Prop.

Locate "_ /\ _".

Print and.

Goal P -> R -> P /\ R.
Proof.
move=> p r.
apply: conj => //.
Qed.

Goal P -> R -> P /\ R.
Proof.
move=> p r.
constructor 1 => //. (* number of constructors to apply *)
Qed.

Goal P -> R -> P /\ R.
Proof.
move=> p r.
split => //.
Qed.

Goal P /\ Q -> P.
Proof.
case.
done.
Qed.

Goal P -> P \/ Q \/ R.
Proof.
move => p.
by left.
Qed.

Goal P \/ Q -> Q \/ P.
Proof.
case => x.
  by right.
by left.
Qed.

Locate "~ _".

Lemma contra_p: (P -> Q) -> (~Q -> ~P).
Proof.
move=> H Hq.
move /H. (* Apply H to the top of the goal *)
by exact: Hq.
Qed.


Locate "exists".

Lemma ex_impl_ex A (P Q: A -> Prop): 
  (exists a, P a) -> (forall x, P x -> Q x) -> (exists b, Q b).
Proof.
move => [a pa] H.
exists a.
by apply H.
Qed.

Inductive my_ex A (P: A -> Prop): Prop := my_ex_intro x of P x.

Goal forall A P, (my_ex A P) <-> exists x, P x.
Proof.
move => A P.
split.
- case => x px.
  by exists x.
- case => x px.
  by exists x.
Qed.

End Connectives.


Require Import Classical_Prop.

Check classic.

Definition peirce_law := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition peirce := peirce_law.
Definition double_neg := forall (P: Prop), ~ (~ P) -> P.
Definition excluded_middle := forall P: Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~( ~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall (P Q: Prop), (P -> Q) -> (~P \/ Q).

Lemma ex1: peirce_law -> double_neg.
Proof.
rewrite /not /peirce_law /double_neg => H P nnp.
apply: (H P (~ ~ P)) => pp.
Admitted.


Set Printing Universes.

Check bool.
Check Set.
Check Prop.
Check list.

Definition S := forall T: Set, list T.
Check S.

Definition R (A: Type) (x: A) : A := x.
Arguments R [A].
Check R tt.

Fail Check R R.


Polymorphic Definition Rp (A: Type) (x: A) : A := x.
Arguments Rp [A].

Check Rp Rp.











