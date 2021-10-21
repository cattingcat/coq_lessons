From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import path choice fintype tuple finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Search (?n.+1 + ?m = (?n + ?m).+1).

Lemma tst n m: (n.+1 + m = (n + m).+1).
Proof. done. Qed.

Fixpoint f n := if n is n'.+1 then (f n').+2 else 0.

Lemma foo : forall n, f (2 * n) = f n + f n.
Proof.
elim => [|n ihn].
- by rewrite muln0.
rewrite !addnS !addSn -/f.
rewrite mulnS.
by rewrite -ihn.
Qed.


(* https://ilyasergey.net/util/ssreflect-manual.pdf *) 

Section Tauto.
Variables A B C : Prop.
Lemma tauto1: A -> A.
Proof. done. Qed.

Lemma tauto2: (A -> B) -> (B -> C) -> A -> C.
Proof. move=> ab bc /ab. exact: bc. Qed.

Lemma tauto3: A /\ B <-> B /\ A.
Proof. by split; case. Qed.
End Tauto.


Section MoreBasics.
Variables A B C : Prop.
Variable P : nat -> Prop.

Lemma foo1: ~(exists x, P x) -> forall x, ~P x.
Proof. move=> nex x px. apply: nex. by exists x. Qed.

Lemma foo2: (exists x, A -> P x) -> (forall x, ~P x) -> ~A.
Proof. move=> [x a_px] xnpx /a_px. exact: xnpx. Qed.
End MoreBasics.

Lemma tuto_subnn: forall n : nat, n - n = 0.
Proof. by elim => [| n IHn] //=. Qed.

Search (?m < ?n.+1).
Lemma tuto_subn_gt0: forall m n, (0 < n - m) = (m < n).
Proof.
elim=> [| m IHm ]; elim=> [| n IHn ] //=.
rewrite subSS IHm //.
Qed.


Lemma tuto_subnKC: forall m n : nat, m <= n -> m + (n - m) = n.
Proof.
elim=> [| m IHm ]; elim=> [| n IHn ] //=.
rewrite subSS addSn => m_le_sn. rewrite IHm //.
Qed.

Search _ (?m + 0 = ?m).
Print "<=".

Lemma my (m p: nat): m + p - p = m.
Proof.
elim: m => [| m IHm ] //=.
  rewrite add0n subnn //=.
rewrite -{2}[p]/(0 + p) .
by rewrite subnDr subn0.
Qed.

Lemma tuto_subn_subA: forall m n p, p <= n -> m - (n - p) = m + p - n.
Proof.
move=> m n p p_leq_n.
rewrite -{2}(tuto_subnKC p_leq_n) subnDA my.
done.
Qed.


Inductive test : nat -> Prop :=
  | C1 : forall n, test n 
  | C2 : forall n, test n 
  | C3 : forall n, test n 
  | C4 : forall n, test n.

Goal forall n, test n -> True.
Proof.
move=> n; case; last 2 [move=> k| move=> l]; idtac.
Admitted.

Lemma find_ex_minn: forall (P: nat -> bool),
  (exists n, P n) -> {m | P m & forall n, P n -> n >= m}.
Proof.
move => P.
have: forall n, P n -> n >= 0 by done.
(* remove by done ->  2 goals *)
have H := forall x, (x, x) = (x, x).
Admitted.

Lemma tuto_subn_subA': forall m n p, p <= n -> m - (n - p) = m + p - n.
Proof.
move=> m n p p_leq_n.
have: forall (m' p': nat), m' + p' - p' = m'.
  elim=> [| m' IHm' ] p' //=.
  rewrite add0n subnn //=.
  rewrite -{2}[p']/(0 + p') .
  by rewrite subnDr subn0.
move=> t.
rewrite -{2}(tuto_subnKC p_leq_n) subnDA t.
done.
Qed.


(* 
    wlog: /term. 
    it creates two subgoals, respectively 
      term -> G 
    and 
      (term -> G)-> G.
*)


Record zmodule_mixin_of(T : Type) : Type := ZmoduleMixin {
  zero : T;
  opp : T -> T;
  add : T -> T -> T;
  addA : associative add;
  addC: commutative add;
  addm0 : left_id zero add;
  add0m : left_inverse zero opp add
}.
Record zmodule: Type := Zmodule {
  carrier :> Type; (* :>  generates coersion *)
  spec : zmodule_mixin_of carrier
}.


Definition bool_zmoduleMixin := ZmoduleMixin addbA addbC addFb addbb.
Definition bool_zmodule := Zmodule bool_zmoduleMixin.

Variable b : bool_zmodule.
Check b.

Definition zmadd (Z : zmodule) := add (spec Z).

Notation "x \+ y" := (@zmadd _ x y)(at level 50,left associativity).

Fail Check false \+ true.
Canonical Structure bool_zmodule.
Check false \+ true.













