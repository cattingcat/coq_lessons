From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.


Lemma andb_true_elim b c: b && c -> c = true.
Proof.
by case/andP.
Restart.
case: c.
- by case: b.
by case: b.
Restart.
case: c; first done.
by case: b.
Restart.
case: c; [done | by case: b].
Restart.
by do 2![done | apply: eqxx | case: b | case: c]. (* 2 - numm of attempts (optional) *)
Qed.

(* do - repetition tactical *)


Inductive evenP n : Prop :=
  | Even0 of n = 0
  | EvenSS m of n = m.+2 & evenP m.

Fixpoint evenb n := if n is n'.+2 then evenb n' else n == 0.


Lemma evenP_contra n : evenP (n + 1 + n) -> False.
Proof.
elim: n=>//[| n Hn]; first by rewrite addn0 add0n; case=>//.
rewrite addn1 addnS addnC !addnS.
rewrite addnC addn1 addnS in Hn.
case=>// m /eqP.
by rewrite !eqSS; move/eqP=><-.
Qed.

Lemma evenb_contra n: evenb (n + 1 + n) -> False.
Proof.
elim: n=>[|n IH] //.
by rewrite addSn addnS.
Qed.

Lemma evenP_plus n m : evenP n -> evenP m -> evenP (n + m).
Proof.
elim=>//n'; first by move=>->; rewrite add0n.
move=> m' -> {n'} H1 H2 H3; rewrite addnC !addnS addnC.
apply: (EvenSS )=>//.
by apply: H2.
Qed.

Lemma evenb_plus n m : evenb n -> evenb m -> evenb (n + m).
Proof.
move: (leqnn n).
elim: n {-2}n.
- by case => //.
move => n Hn.
case=>//.
case=>// n0.
by move/ltnW /Hn=>//.
Qed.

Lemma nat2_ind (P: nat -> Prop):
  P 0 -> 
  P 1 -> 
  (forall n, P n -> P (n.+2)) -> 
  forall n, P n.
Proof.
move => H0 H1 H n.
suff: (P n /\ P (n.+1)) 
  by case.
by elim: n=>//n; case=> H2 H3; split=>//; last by apply: H.
Qed.

Lemma evenb_plus' n m : evenb n -> evenb m -> evenb (n + m).
Proof.
by elim/nat2_ind : n.
Qed.

Inductive beautiful (n: nat) : Prop :=
| b_0 of n = 0
| b_3 of n = 3
| b_5 of n = 5
| b_sum n' m' of beautiful n' & beautiful m' & n = n' + m'.

Search _.*2.
Search mul0n.
Search (_.+1 * _).

Theorem b_times2 n: beautiful n -> beautiful (2 * n).
Proof.
by move => H; rewrite mulnC muln2 -addnn; apply (b_sum _ n n) => //.
Qed.

Lemma b_timesm n m: beautiful n -> beautiful (m * n).
Proof.
elim m.
  move => H //; by apply b_0.
move => m' IHm' bn.
rewrite mulSn.
apply (b_sum _ n (m' * n)) => //.
by apply IHm'.
Qed.


Inductive gorgeous (n: nat) : Prop :=
| g_0 of n = 0
| g_plus3 m of gorgeous m & n = m + 3
| g_plus5 m of gorgeous m & n = m + 5.

Lemma sum_gorgeous (n m: nat) : gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
elim => [_ -> | n' m' gm' IH -> /IH gs | n' m' gm' IH -> /IH gs ] //.
- rewrite addnC addnA (addnC m m').
  by apply (g_plus3 _ (m' + m)).
- rewrite addnC addnA (addnC m m').
  by apply (g_plus5 _ (m' + m)).
Qed.

Lemma beautiful_gorgeous (n: nat) : beautiful n -> gorgeous n.
Proof.
elim => [_ -> | _ -> | _ -> | h n' m' bn' gn' bm' gm' ->].
- by apply g_0.
- apply (g_plus3 _ 0). apply g_0 => //.
  done.
- apply (g_plus5 _ 0). apply g_0 => //.
  done.
by apply sum_gorgeous.
Qed.

Lemma gorgeous_beautiful (n: nat) : gorgeous n -> beautiful n.
Proof.
elim => [_ -> | n' m gm bm -> | n' m gm bm ->] //.
- by apply b_0.
- apply (b_sum _ m 3) => //.
  by apply b_3.
- apply (b_sum _ m 5) => //.
  by apply b_5.
Qed.

Search or3.
Print or3.
Locate or3.
Search (_ * _.+1).
Search (?a + _ = ?a + _ -> _ = _).
Search ((_ <= _)).
Search (maxn).



About eqP.

Search (_ || false).
About leq_eqVlt.

Lemma repr3 n : n >= 8 ->
  exists k, [\/ n = 3 * k + 8, n = 3 * k + 9 | n = 3 * k + 10].
Proof.
elim: n => [ contra | n IH le7] //.
case g: (7 < n).
- case: (IH g) => x [h8 | h9 | h10].
  + exists x. constructor 2. by rewrite h8 -addnS.
  + exists x. constructor 3. by rewrite h9 -addnS.
  + exists x.+1. constructor 1. by rewrite h10 mulnSr -addnS -addnA.
rewrite -ltnS in g.
rewrite leq_eqVlt g Bool.orb_false_r eqSS in le7.
exists 0. constructor 1.
case: eqP le7 => H _ //.
by rewrite H.
Qed.

Lemma gorg3 n : gorgeous (3 * n).
Proof.
elim: n => [| n IHn ] //.
  by constructor.
rewrite mulnSr.
by apply (g_plus3 _ (3 * n)).
Qed.

Lemma gorg_criteria n : n >= 8 -> gorgeous n.
Proof.
move => /repr3 [k [-> | h2 | h3]].
- apply (g_plus3 _ (3 * k + 5)) => //.
  apply (g_plus5 _ (3 * k)) => //.
  apply gorg3.
  by rewrite -addnA.
- have g: 9 = 3 * 3. 
    by done.
  rewrite h2 g -mulnDr.
  by apply gorg3.
- have g: 10 = 5 + 5.
    by done.
  rewrite h3 g addnA.
  apply (g_plus5 _ (3 * k + 5)) => //.
  apply (g_plus5 _ (3 * k)) => //.
  by apply gorg3.
Qed.

Lemma gorg_refl' n: n >= 8 -> reflect (gorgeous n) true.
Proof.
move => /gorg_criteria H.
by constructor.
Qed.


Inductive tree : Set :=
| leaf
| node of tree & tree.

Fixpoint height t :=
  if t is node t1 t2 then (maxn (height t1) (height t2)).+1 else 0.

Lemma height_node t1 t2: 
  height (node t1 t2) = (maxn (height t1) (height t2)).+1.
Proof. done. Qed.

Fixpoint leaves t :=
  if t is node t1 t2 then leaves t1 + leaves t2 else 1.

Lemma leaves_node t1 t2: 
  leaves (node t1 t2) = leaves t1 + leaves t2 .
Proof. done. Qed.

Locate "[ \/ _ , _ | _ ]".

Fixpoint complete t :=
  if t is node t1 t2 then complete t1 && complete t2 && (height t1 == height t2)
  else true.

Lemma complete_node t1 t2: 
  complete (node t1 t2) = complete t1 && complete t2 && (height t1 == height t2).
Proof. done. Qed.


Theorem complete_leaves_height t : complete t -> leaves t = 2 ^ height t.
Proof.
elim: t => [|t IHt t' IHt'] //.
rewrite complete_node => /andP [/andP H2].
move: H2 => [/IHt lt /IHt' lt'] Eh.
rewrite leaves_node height_node.
case: eqP Eh => // Eh.
by rewrite Eh maxnn lt lt' Eh expnS addnn mul2n => _.
Qed.
