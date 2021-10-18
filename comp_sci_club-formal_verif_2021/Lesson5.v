From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.

Module Lesson5.
(* SSReflect tactics *)

Lemma modus_ponens (A B: Prop): A -> (A -> B) -> B.
Proof.
  move=> a.
  apply. (* Goal is a stack                           *)
         (* apply takes top of the stack and apply it *)
  exact: a.
Qed.

Lemma modus_ponens' (A B: Prop): A -> (A -> B) -> B.
Proof.
  move=> a ab.
  apply: ab.
  exact: a.
Qed.

Definition and1 (A B: Prop):
  A /\ B -> A.
Proof.
  case. (* stack operation again. take top of stack, destruct it, and put back to stack *)
  move=> pa _.
  exact: pa.
Qed.

Definition andC (A B: Prop):
  A /\ B -> B /\ A.
Proof.
  case=> pa pb.
  split.
  - exact: pb.
  - exact: pa.
Qed.

Definition orC (A B: Prop):
  A \/ B -> B \/ A.
Proof.
  case.
  - right.
    exact: a.
  left.
  exact: b.
Qed.

Definition andD (A B C: Prop):
  (A \/ B) /\ C -> (A /\ C) \/ (B /\ C).
Proof.
  case.
  case => [a|b] c.
    by left.
  by right.
Qed.

Definition andD1 (A B C: Prop):
  (A \/ B) /\ C -> (A /\ C) \/ (B /\ C).
Proof.
  by case => [[a|b] c]; [left | right].
Qed.


Lemma HilbertSaxion A B C: (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
move: abc. (* move back    "move: (abc)." will move to stack and safe it in context *)
apply.     (* apply top of the stack to goal *)
  exact: a.
apply: ab. (* apply from context *)
exact: a.
Qed.

(* => - move from stack to ctx
   :  - move from ctx to stack and apply tactic from left *)

(* by [].  -  done. *)


Lemma HilbertSaxion1 A B C: (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
by apply: abc; [done | apply: ab].
Qed.

Lemma HilbertSaxion2 A B C: (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
apply: abc=> //.
by apply: ab.
Qed.


Section RewriteTactic.
Variable (A: Type).
Implicit Types x y z : A.
Lemma esym x y :
  x = y -> y = x.
Proof.
move=> eq_xy.
rewrite eq_xy.
done.
Qed.

Lemma esym_short x y :
  x = y -> y = x.
Proof.
move=> ->.
done.
Qed.

Lemma trans x y z:
  x = y -> y = z -> x = z.
Proof.
move=> ->.
done.
Qed.

End RewriteTactic.


Lemma addnA : associative addn.
Proof.
rewrite /associative.
move => x y z.
Restart.
move => x y z.
elim: x => [|x' IHx] //.
Show Proof.
Search (_.+1 + _).
by rewrite addSn IHx.
Qed.

Lemma addnA2 : associative addn.
Proof.
elim => [|x' IHx] y z //. (* elim top stack *)
by rewrite addSn IHx.
Qed.

End Lesson5.
