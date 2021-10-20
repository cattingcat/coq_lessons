From mathcomp Require Import all_ssreflect.

Module Lesson7.

(* Notation: 
  Lemma all_filter T (p: pred T) (s: seq T) :
    all p s -> [seq x <- s | p x] = s.
*)

Print pred.
Print all.
Print filter.
Locate "[ 'seq' _ '<-' _ | _]".

Print is_true.
Locate "^~".

Lemma all_filter T (p: pred T) (s: seq T) :
  all p s -> filter p s = s.
Proof.
(* rewrite /is_true. *)
elim: s => //= x s IHs. (* //=  =  // //=  resolve simpl goals and simpl. *)
(* need to convert from bool form - to Prop form *)
move=> /andP. (* apply function to current top, /[tact] - apply tactic to currr top *)
About andP.
case=> -> pall. (* ->  - move to context and rewrite *)
by rewrite IHs.
Restart.
by elim: s => //= x s IHs /andP [-> /IHs->].
Qed.

About andP.
About reflect.
Print Bool.reflect.

Goal forall P, reflect P true -> P.
Proof.
move=> P.
exact: (fun (r: reflect P true) =>
         (match r 
            in reflect _ b
            return b = true -> P
          with
          | ReflectT p  => fun _ => p
          | ReflectF np => fun _ => ltac:(done)
          end) erefl).
Restart.
move=> P.
case.
Restart.
move=> P R.
case E:true / R. (* remember true eqn:E *)
  done.
done.
Restart.
by move=> P; case E:true /.
Restart.
by move=> P; case E:_ /.
Qed.

Goal forall P, reflect P false -> ~P.
Proof.
by move => P; case E:false /.
Qed.

Lemma introT_my P b:
  reflect P b -> (P -> b).
Proof.
case.
- done.
by move => /[apply].
Qed.

Lemma elimT_my P b:
  reflect P b -> (b -> P).
Proof.
case E:b /.
- done.
move => c.
discriminate c. (* ssreflect ??? *)
Qed.

Lemma reflect_lem P b :
  reflect P b -> P \/ ~P.
Proof.
by case; [left|right].
Qed.

Lemma andP_my (b c: bool) :
  reflect (b /\ c) (b && c).
Proof.
case: b.
- case: c.
  - constructor. done.
  - constructor. by case.
- case: c; constructor; by case.
Restart.
by case: b; case: c; constructor => //; case.
Qed.

Lemma nandP_my b c:
  reflect (~~b \/ ~~c) (~~(b && c)).
Proof.
case: b; case: c; constructor; intuition. (* intuition - solver for intuitionistic logic (&& || ~~) *)
Qed.

Lemma inP_my (b: bool):
  reflect b b.
Proof.
by case b; constructor.
Qed.

Lemma scecial_support_reclect_pred b c:
  b && c -> b /\ c.
Proof.
move /andP.
Show Proof.
About elimTF.
done.
Restart.
move=> Hb.
Check (@elimTF (b /\ c) (b && c) true (@andP b c) Hb).
move: Hb.
move /(@elimTF (b /\ c) (b && c) true (@andP b c)).
exact: id.
Qed.

Lemma scecial_support_reclect_pred2 b c:
  b && c = false -> ~(b /\ c).
Proof.
move /andP.
exact: id.
Restart.
move=> Hb.
Check (@elimTF (b /\ c) (b && c) false (@andP b c) Hb).
move: Hb.
exact: (@elimTF (b /\ c) (b && c) false (@andP b c)).
Qed.



Lemma scecial_support_reclect_pred_rev (b c: bool):
  b /\ c -> b && c.
Proof.
move=> h.
apply/andP.
Show Proof.
About introTF.
exact: h.
Qed.

Lemma eqnP_my (n m : nat):
  reflect (n = m) (eqn n m).
Proof.
About iffP.
apply: (iffP idP).
by elim: n m => [|n IHn] [|m] //= /IHn ->.
move=> ->; elim: m => [|m IHm] //=.
Qed.

Lemma nseqP (T: eqType) n (x y: T):
  reflect (y = x /\ n > 0) (y \in nseq n x).
Proof.
rewrite mem_nseq.
rewrite andbC.
apply: (iffP andP).
- case. move/eqP. done.
case=> ->->. done.
Qed.

About eqType.
About mathcomp.ssreflect.eqtype.Equality.Exports.eqType.

Lemma leq_max m n1 n2:
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
About leq_total.
case/orP: (leq_total n2 n1) => [le_n21 | le_n12].
Search (maxn ?n ?m = ?n).
rewrite (maxn_idPl le_n21).

Abort.

Search reflect inside seq.
Search reflect inside ssrnat.


Example for_ltngtP m n:
  (m <= n) && (n <= m) ->
  (m == n) || (m > n) || (m + n == 0).
Proof.
by case ltngtP.
Qed.

About ltngtP.
About compare_nat.
(* Variant compare_nat - Inductive without self refs *)

Example for_ltngtP2 m n:
  (m <= n) && (n <= m) ->
  (m == n) || (m > n) || (m + n == 0).
Proof.
case: ltngtP.
- done.
- done.
- done.
Qed.

(* rewrite [patter]rule. *)

End Lesson7.
