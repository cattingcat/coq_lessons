From Coq Require Import Program.
From QuickChick Require Import QuickChick.
From mathcomp Require Import all_ssreflect.
Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Insertion.

Section InsertionSort.
Variable T: eqType.
Variable leT: rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.

Fixpoint insert e s: seq T :=
  if s is x :: s' 
    then
      if leT e x then [:: e & s] else x :: insert e s'
    else 
      [:: e].

Fixpoint sort s: seq T :=
  if s is x :: s'
    then insert x (sort s')
    else [::].


Fixpoint sorted' s: bool :=
  if s is x1 :: ((x2 :: s') as tail)
    then leT x1 x2 && (sorted' tail)
    else true.

Print sorted.
Print path.

Lemma sorted_cons x s:
  sorted leT (x :: s) -> sorted leT s.
Proof.
by case: s => //= h t /andP [_ H].
Qed.

Definition fake_sort s: seq T := [::].
Lemma sorted_fake_sort s: sorted leT (fake_sort s).
Proof. done. Qed.

Print perm_eq.

Lemma insert_sorted e s:
  sorted leT s ->
  sorted leT (insert e s).
Proof.
elim: s => [// | x1 s IHs].
move=> /=.
move=> path_x1_s.
case: ifP => [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
Abort.

Hypothesis leT_total: total leT.
Print total.

Lemma insert_sorted e s:
  sorted leT s ->
  sorted leT (insert e s).
Proof.
elim: s => [// | x1 s IHs].
move=> /=.
move=> path_x1_s.
case: ifP => [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
have:=leT_total e x1.
rewrite {}e_gt_x1.
move=> /= x1_le_e.
About path_sorted.
move: path_x1_s => {}/path_sorted/IHs.
case: s => [| x2 s] /=; first by rewrite x1_le_e.
case: ifP => /=.
- move => -> ->. by rewrite x1_le_e.
Abort.

Lemma insert_path z e s:
  leT z e ->
  path leT z s ->
  path leT z (insert e s).
Proof.
elim: s z => [/=| x1 s IHs] z. (* gen z *)
- by move=> ->.
move => z_le_e /=.
case/andP=> z_le_x1 path_x1_s.
case: ifP => /=.
- by rewrite z_le_e path_x1_s => ->.
move => e_gt_x1.
rewrite z_le_x1.
have:= leT_total e x1.
rewrite {}e_gt_x1 /= => x1_le_e.
exact: IHs.
Qed.

Lemma insert_sorted e s :
  sorted leT s ->
  sorted leT (insert e s).
Proof.
rewrite /sorted.
case: s=> // x s.
move=> /=.
case: ifP; first by move=> /= ->->.
move=> e_gt_x.
apply: insert_path.
have:= leT_total e x.
by rewrite e_gt_x /= => ->.
Qed.

Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
elim: s => [//|x s IHs] /=.
rewrite insert_sorted => //.
Qed.

End InsertionSort.

Arguments sort {T} _ _.
Arguments insert {T} _ _ _.


Section SortIsPermutation.

Variable T : eqType.
Variables leT : rel T.

Lemma count_insert p e s :
  count p (insert leT e s) = p e + count p s.
Proof.
by elim: s => //= x s; case: ifP=> _ //= ->; rewrite addnCA.
Qed.

About perm_eql.


Lemma perm_sort s : perm_eql (sort leT s) s.
Proof.
Search _ (perm_eq ?s1 =1 perm_eq ?s2).
apply/permPl/permP.
elim: s=> //= x s IHs p.
by rewrite count_insert IHs.
Qed.

(*| This is why we state `perm_sort` lemma using
`perm_eql` -- it can be used as an equation like
so |*)

Lemma mem_sort s : sort leT s =i s.
Proof. by apply: perm_mem; rewrite perm_sort. Qed.

Lemma sort_uniq s : uniq (sort leT s) = uniq s.
Proof. by apply: perm_uniq; rewrite perm_sort. Qed.

End SortIsPermutation.


Section SortProperties.
Variable T : eqType.
Variables leT : rel T.

Lemma sorted_sort s :
  sorted leT s -> sort leT s = s.
Proof.
elim: s=> // x1 s IHs S.
move: (S) => {}/sorted_cons/IHs /= ->.
move: S=> /=.
case: s=> //= x2 s.
by case/andP=> ->.
Qed.

End SortProperties.
End Insertion.


Module Merge.
Section MergeSortDef.
Context {disp : unit} {T : orderType disp}.
Implicit Types s t : seq T.

Fixpoint split s : seq T * seq T :=
  match s with
  | [::] => (s, s)
  | [:: x] => (s, [::])
  | [:: x, y & s] =>
      let '(t1, t2) := split s in
      (x :: t1, y :: t2)
  end.

Arguments split : simpl nomatch.

Lemma split_lt1 s2 s1 s :
  1 < size s ->
  split s = (s1, s2) ->
  (size s1 < size s).
Proof.
Admitted.

Lemma split_lt2 s1 s2 s :
  1 < size s ->
  split s = (s1, s2) ->
  (size s2 < size s).
Proof.
Admitted.

Fail Fixpoint merge s t : seq T :=
  match s, t with
  | [::], _ => t
  | _, [::] => s
  | x :: s', y :: t' =>
      if (x <= y)%O then x :: merge s' t else y :: merge s t'
  end.

(* Nested `fix`-combinator idiom *)
Fixpoint merge s t : seq T :=
  let fix merge_s t :=
    match s, t with
    | [::], _ => t
    | _, [::] => s
    | x :: s', y :: t' =>
      if (x <= y)%O
      then x :: merge s' t
      else y :: merge_s  t'
    end
  in merge_s t.


Fail Fixpoint sort s : seq T :=
  match s with
  | [::] => s
  | [:: _] => s
  | _ => let '(s1, s2) := split s in merge (sort s1) (sort s2)
  end.

(*| There is a clever way to implement merge-sort
as a system of recursive functions but we are not
going to go this direction here. |*)

Fail Fixpoint sort s : seq T :=
  match s with
  | [::] => s
  | [:: _] => s
  | _ => let '(s1, s2) := split s in merge (sort s1) (sort s2)
  end.

(*| A little trick: one can disable termination checker |*)

Print Typing Flags.

Unset Guard Checking.

Print Typing Flags.

(*| Now one can define the usual top-down
merge-sort function: |*)
Fixpoint sort_unguarded s : seq T :=
  match s with
  | [::] => s
  | [:: _] => s
  | _ => let '(s1, s2) := split s in
         merge (sort_unguarded s1) (sort_unguarded s2)
  end.
Print Assumptions sort_unguarded.
Set Guard Checking.

(*| Here, the nested `fix` design pattern would not work |*)

Program Fixpoint sort s {measure (size s)} : seq T  :=
  match s with
  | [::] => s
  | [:: _] => s
  | _ => let '(s1, s2) := split s in
         merge (sort s1) (sort s2)
  end.
Next Obligation.
apply/ltP; rewrite (@split_lt1 s2) //.
by case: s sort H0 H Heq_anonymous=> // x1 [] // _ _ /(_ x1).
Qed.
Next Obligation.
apply/ltP; rewrite (@split_lt2 s1) //.
by case: s sort H0 H Heq_anonymous=> // x1 [] // _ _ /(_ x1).
Qed.
Next Obligation. by []. Qed.


End MergeSortDef.

(*|
Example: using `orderType` instances
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
|*)
Section MergeSortTest.

Compute merge [:: 1; 3; 5] [:: 2; 4; 6].

Compute sort_unguarded [:: 6; 4; 2; 1; 3; 5].

Compute sort [:: 6; 4; 2; 1; 3; 5].

End MergeSortTest.


Section MergeSortCorrect.

Context {disp : unit} {T : orderType disp}.
Implicit Types s t : seq T.

(*| (Optional) exercise |*)
Lemma sort_sorted s :
  sorted (<=%O) (sort s).
Proof.
Admitted.

End MergeSortCorrect.
End Merge.


(*|
`Acc`-predicate
---------------
|*)

(*| Let's see why `Merge.sort` works: |*)
Print Merge.sort.
Print Fix_sub.
Print Fix_F_sub.
Print Acc.


(*| `Acc R x` can be read as "x is accessible
under relation R if all elements staying in
relation R with it are also accessible" |*)

(*| Coq allows us do structural recursion on a
term of type `Acc` which lives in `Prop` while
building a term of a type living in `Type`.
(structural recursion involves pattern-matching).
But the accessibility predicate is defined to be
non-informative (one constructor!). |*)


(*| This allows one do lots of interesting stuff, including
to counting up |*)

(*|
Accessibility predicate on natural numbers
========================================== *)

Section AccFrom.

Variable (p : pred nat).

(*| The `acc_from` predicate lets us count up: we
are not allowed to use `acc_from` to drive
computation (extract information from proofs of
propositions to make computationally relevant
terms), but you can define a recursive function
from a type like this to a type in `Type` and the
*termination checker* is totally (pun intended)
happy with it. We'll see this sort of example at
the end. |*)
Inductive acc_from i : Prop :=
| AccNow of p i
| AccLater of acc_from i.+1.

End AccFrom.

(*| Check out the corresponding induction principle. |*)
About acc_from_ind.


(*|
Simple examples
=============== |*)

Section SimpleExamples.

(*| Let's do a couple of proofs to get the gist of `acc_from` |*)

(*| 1. The property of "being equal to 42" is accessible from 0: |*)
Goal acc_from (fun n => n == 42) 0.
Proof.
do 42 apply: AccLater.
by apply: AccNow.
Qed.


(*| 2. But it's inaccessible from 43: |*)
Goal acc_from (fun n => n == 42) 43 -> False.
Proof.
(*| If you start proving the current goal
directly, you will quickly get stuck because your
goal is too specialised. Clearly, you need
induction over the accessibility predicate, but
`elim` messes up your base case (look at the type
of `acc_from_ind`). |*)
elim.
Show Proof.
(* the first subgoal is unprovable *)
Abort.


(*| We could try and create a more useful
induction principle for our case but we might as
well just use a low-level tactic `fix` which
translates directly to Gallina's fixed-point
combinator. |*)

Goal acc_from (fun n => n == 42) 43 -> False.
Proof.
fix inacc 1.
Show Proof.
(*| To recursively call `inacc` on a structurally
smaller argument we need to case analyse the top
of the goal stack: |*)
case.
(*| The base case is easy now: |*)
- by [].
(*| But here we are stuck. |*)
Abort.


(*| So we generalize the goal to make the proof go
through. |*)
Lemma inacc_from43 :
  forall x, 42 < x -> acc_from (fun n => n == 42) x -> False.
Proof.
fix inacc 3.
Show Proof.
move=> x x_gt42.
case=> [/eqP E|].
- by rewrite E in x_gt42.
apply: inacc.
by apply: (ltn_trans x_gt42).
Qed.

End SimpleExamples.


(*|
Getting a concrete value from an abstract existence proof
========================================================= |*)

Section Find.

Variable p : pred nat.

Lemma find_ex :
  (exists n, p n) -> {m | p m}.
Proof.
move=> exp.

have: acc_from p 0.
(*| `acc_from` lives in `Prop`, so we are allowed
to destruct `exp` in this context, see below. |*)
- case: exp => n.
  rewrite -(addn0 n).
  elim: n 0=> [|n IHn] j.
  - by left.
  rewrite addSnnS.
  right.
  apply: IHn.
  by [].

move: 0.
fix find_ex 2=> m IHm.
case pm: (p m).
- by exists m.
apply: find_ex m.+1 _.
(*| Observe we can only destruct `IHm` at this
point where we are tasked with building a proof
and not a computationally relevant term. |*)
case: IHm.
- by rewrite pm.
by [].
Defined.


















End Insertion.
