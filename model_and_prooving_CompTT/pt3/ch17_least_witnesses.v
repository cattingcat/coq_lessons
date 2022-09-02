From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Psatz.

Definition safe p (n: nat) := forall k, p k -> k >= n.
Definition least p (n: nat) := p n /\ safe p n.

(* 17.1.1 *)
Lemma f1: forall p n n', least p n -> least p n' -> n = n'.
Proof.
  rewrite /least /safe.
  move => p n n' [pn H] [pn' H'].
  move: (H n' pn') (H' n pn) => G G'.
  apply/eqP.
  rewrite eqn_leq.
  by apply/andP.
Qed.

Lemma f2: forall p, safe p 0.
Proof.
  by move => p k H.
Qed.

Lemma f3: forall (p: nat -> Prop) n, safe p n -> ~ (p n) -> safe p (S n).
Proof.
  rewrite /safe.
  move => p n HS Np k H.
  move: (HS k H).
  rewrite leq_eqVlt.
  case/orP.
    move => /eqP E; exfalso.
    apply Np; rewrite E.
    by apply H.
  by [].
Qed.

Lemma f4: forall (p: nat -> Prop) (n m: nat), safe p m -> least p n -> m <= n.
Proof.
  rewrite /least /safe.
  move => p n m Hs [Pn Hl].
  by apply Hs.
Qed.




(* 17.1.2 *)
Lemma helper1: forall a b c, a >= c -> a + b - c = a - c + b.
Proof.
  elim => [b c |a' IH b c].
    case c => [H|n].
      by rewrite add0n subn0.
    by move => H; exfalso.
  rewrite leq_eqVlt => /orP.
  case.
    move => /eqP <-.
    by rewrite addKn subnn add0n.
  rewrite ltnS => L.
  move: (IH 1 c L).
  rewrite 2!addn1 => ->.
  move: (IH b.+1 c L).
  rewrite addnS addSn => ->.
  by rewrite addSn addnS.
Qed.

Lemma helper2: forall a b, a - b == 0 -> a - b.+1 = 0.
Proof. move => a b.
  elim: a b => [b //| a' IH b].
  case b => [//|b'].
  rewrite 2!subSS.
  apply IH.
Qed.

Theorem euclid_div: forall x y a b, 
  (x = a * y.+1 + b /\ b <= y) <-> (least (fun a => x < a.+1 * y.+1) a /\ b = x - a * y.+1).
Proof.
  move => x y a b.
  split.
    move => [Hx Hb].
    split; last first.
      rewrite Hx.
      by rewrite addnC addnK.
    rewrite /least /safe.
    split.
      rewrite Hx mulSn addnC ltn_add2r.
      by rewrite ltnS.
    move => k.
    rewrite Hx mulSn addnC addSn ltnS.
    move => /subnKC.
    case (ltngtP a k) => Hk.
    - set q := b + a * y.+1.
      set w := y + k * y.+1.
      rewrite subnKC.
        by [].
      rewrite leq_add => //.
      rewrite leq_pmul2r => //.
      auto.
    - set q := b + a * y.+1.
      set w := y + k * y.+1.
      have G: w < q.
        rewrite /q /w.
        case: a Hx Hk q => [|a'] Hx Hk q => //.
        rewrite mulSn addnA.
        move: Hk => /ltnSE Hk.
        rewrite -addSn.
        apply leq_add.
          rewrite ltn_addl => //.
        apply leq_mul => //.
      have G': w - q = 0.
        move: G.
        case q => [//| n'].
        rewrite /(_ < _) subSS.
        by apply helper2.
      rewrite G' addn0.
      move: G.
      rewrite ltn_neqAle => /andP [T _].
      move: T => /eqP Contra C.
      exfalso. apply Contra.
      by rewrite C.
    rewrite Hk.
    set q := b + k * y.+1.
    set w := y + k * y.+1.
    have G: q <= w.
      by rewrite /q /w leq_add2r.
    by rewrite (subnKC G).
  rewrite /least /safe => [[[H H''] H']].
  have G: ~(x < a * y.+1).
      move => G'.
      case: a H H'' H' G' => [H H'' H'| n H H'' H'].
        by rewrite mul0n.
      move => G'.
      move: (H'' _ G').
      by rewrite ltnn.
  split.
    rewrite H'.
    rewrite subnKC => //.
    (* a*y.+1 <= x < a.+1*y.+1 *)
    rewrite leqNgt.
    by apply/negP.
  move: G => /negP.
  rewrite -leqNgt => G.
  rewrite H'.
  move: H.
  rewrite mulSn addSn => /ltnSE.
  by rewrite leq_subLR addnC.
Qed.

(* 17.1.3 *)
Lemma substraction: forall x y z, 
  x - y = z <-> least (fun z' => x <= y + z') z.
Proof. Admitted.

(* 17.1.4 *)
Lemma ex1714: forall (p: nat -> Prop) n, safe p (n.+1) <-> safe p n /\ ~ (p n).
Proof.
  move => p n.
  rewrite /safe.
  split.
    move => H.
    split.
      move => k pk.
Admitted.
