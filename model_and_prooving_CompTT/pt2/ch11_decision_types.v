From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "+".
Print sumor. (* decision type, 
                  left - result of type X, 
                  right - proof that result doesn't exist *)
Print sumbool.
Print sum.

(* Decidable type *)
Definition D (X: Type): Type := X + {X -> False}.

(* 11.1.1 *)
Theorem decider_eq_fw (X: Type) (P: X -> Prop):
  (forall x, D(P x)) -> {f & forall x, P x <-> f x = true}.
Proof.
  move => H.
  exists (fun x => match (H x) with
                   | inleft _ => true
                   | inright _ => false
                  end).
  move => x.
  split.
    move => Px.
    case (H x).
      by [].
    move => false.
    exfalso.
    apply (false Px).
  case (H x).
    by [].
  by [].
Qed.

Theorem decider_eq_bw (X: Type) (P: X -> Prop):
  {f & forall x, P x <-> f x = true} -> (forall x, D(P x)).
Proof.
  move => [f H] x.
  move: (H x) => [fw bw].
  rewrite /D.
  case Hfx: (f x).
    left.
    apply bw.
    apply Hfx.
  right.
  move /fw.
  by rewrite Hfx.
Qed.

(* 11.1.3 *)
Goal D True.
Proof. left. apply I. Qed.

Goal D False.
Proof. by right. Qed.

Goal forall X Y, D X -> D Y -> (D (X -> Y)).
Proof. 
  move => X Y DX DY.
  case DX; case DY.
  - move => y x.
    by left.
  - move => ny x. 
    right.
    move => h.
    apply ny.
    apply h.
    by apply x.
  - move => y nx.
    left.
    move => x.
    apply y.
  - move => nx ny.
    left.
    move => x.
    exfalso.
    by apply (ny x).
Qed. 


Lemma t: false = true -> False.
Proof. by []. Qed.
Print t.

Search (_ = _ -> False).

Print eq_ind.
(* 11.1.4 *)
Definition ex1 (X: Type) (f: X -> bool) (x: X): D (f x = true) := 
  match (f x) with
  | true => inleft (erefl)
  | false => inright (fun a => eq_ind false (fun e : bool => if e then False else True) I true a)
  end.


(* Discrete type, could be decided equality *)
Definition E (X: Type): Type := forall (x y: X), D (x = y).

(* 11.2.1 *)
Lemma bool_discrete: E bool.
Proof.
  move => x y.
  case x; case y.
  - by left.
  - by right.
  - by right.
  - by left.
Qed.

Lemma prod_discrete: forall X Y, E X -> E Y -> E (X * Y).
Proof.
  move => X Y Ex Ey [x1 y1] [x2 y2].
  case (Ex x1 x2); case (Ey y1 y2).
  - move => -> ->.
    by left.
  - move => contra Hx.
    right.
    case => Hx' Hy.
    by apply (contra Hy).
  - move => Hy contra.
    right.
    case => Hx Hy'.
    by apply (contra Hx).
  - move => Hy contra.
    right.
    case => Hx Hy'.
    by apply (contra Hx).
Qed.

Print option.

(* 11.3.2 *)
Lemma opt_discrete: forall X, E X -> E (option X).
Proof.
  move => X H x y.
  case x; case y.
  - move => a b.
    case (H a b).
    + move => ->.
      by left.
    + right.
      move => contra.
      apply f.
      by case: contra.
  - by right. 
  - by right.
  - by left.
Qed.
  
Inductive fin: nat -> Type :=
  | fin_intro : forall n, fin n -> fin (S n).
