From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* disjointness *)
Goal forall x, S x <> 0.
Proof. by []. Qed.

(* injectivity *)
Lemma inj: forall x y, S x = S y -> x = y.
Proof. move => x y. by case. Qed.

(* progress *)
Lemma progr: forall x, S x <> x.
Proof. move => x. elim: x => [//| n IH].
  by move /inj.
Qed.

(* Decidable type *)
Definition D (X: Type): Type := X + {X -> False}.

(* 15.1.2 *)
Lemma discrete: forall (x y: nat), D (x = y).
Proof.
  elim.
    - case. 
        by left.
      move => n. right. by [].
    - move => n IH.
      case.
        by right.
      move => y.
      case (IH y).
        left. by rewrite e.
        right. move => H.
          apply f.
          move: H.
          by case.
Qed.

Theorem double_ind: forall (p: nat -> nat -> Type), 
  (forall x, p x 0) ->
  (forall x y, p x y -> p y x -> p x (S y)) ->
  (forall x y, p x y).
Proof.
  move => p H0 H1 x y.
  move: y.
  elim.
    by apply H0.
  move => y H.
  apply H1.
    apply H.
  move: x H.
  elim => [H| n H H'].
    apply H0.
  apply H1.
Admitted.

Lemma trans: forall x y z, x < y -> y < S z -> x < z.
Proof.
  elim.
    move => y z contr.
    exfalso.
    admit.
  move => n H.
    move => x z H.
    by exfalso.
  move => n H x z H1 H2.
Admitted.

Theorem complete_ind: forall (p: nat -> Type),
  (forall x, (forall y, y < x -> p y) -> p x) ->
  (forall x, p x).
Proof.
  move => p H x.
  have G: forall n x, x < n -> p x.
    elim.
      move => x' contra. by exfalso.
    move => n IH x' L.
    apply H => y Ly. 
    apply IH.
    by apply (trans (y:=x')).
  apply H.
  apply G.
Qed.
    
    