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

Lemma leq0: forall x, x <= 0 -> x = 0.
Proof.
  elim => [//|n IH].
    move => contra.
    by exfalso.
Qed.

(* 15.5.2 *)
Lemma leq_unpack: forall x y, x <= y -> x < y \/ x = y.
Proof.
  move => x y.
  rewrite leq_eqVlt.
  move => /orP.
  case.
    right.
    by move: a => /eqnP.
  by left.
Qed.

(* 15.5.5 *)
Lemma existential_characrerization: forall x y, x <= y -> exists k, x + k = y.
Proof.
  move => x y.
  elim: y x => [y /leq0 -> | y' IH x H].
    by exists 0.
  move: H => /leq_unpack.
  case.
    - move => /ltnSE H.
      move : (IH x H) => [k H'].
      exists k.+1.
      by rewrite -H' addnS.
  move => ->.
  exists 0.
  by rewrite addn0.
Qed.


(* 15.6.2 *)
Lemma trans: forall x y z, x < y <= z -> x < z.
Proof.
  move => x y z /andP [Hl Hr].
  move: (existential_characrerization Hl) (existential_characrerization Hr).
  move => [k <-] [k' Hr'].
  move: Hr'.
  rewrite 2!addSn.
  rewrite addnC addnCA -addnS.
  move => <-.
  rewrite /(_ < _) addnS subSS.
  rewrite subnDA.
  rewrite subnn.
  rewrite sub0n.
  by [].
Qed.

(* 15.7.1 *)
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
    have G: y < x' <= n.
      apply /andP.
      split => [//|].
      move: L.
      rewrite [x' < n.+1]/(x'.+1 <= n.+1).
      by rewrite subSS.
    by apply (trans G).
  apply H.
  apply G.
Qed.
    
    