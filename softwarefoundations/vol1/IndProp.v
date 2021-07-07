From LF Require Export Logic.
From Coq Require Import Lia.

Module IndProp.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

(*
  Definition ev (n : nat) : Prop := even n = true.
  Defivition Ev (n : nat) : Prop := exists (x : nat), n = double x.
*)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).


Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Search (nat -> nat).

Theorem ev_double : forall n,
  ev (Logic.double n).
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    apply ev_0.
  - simpl.
    apply ev_SS.
    apply H.
Qed.

Theorem ev_inversion : forall (n : nat), 
  ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n [ | n' Hev ].
  - left. reflexivity.
  - right. exists n'. split.
    + reflexivity.
    + apply Hev.
Qed. 

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.



Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* We must prove that n is even from no assumptions! *)
Abort.

Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  remember (S (S n)) as k eqn:Hk.
  destruct E as [|n' E'] eqn:EE.
  - discriminate Hk.
  - injection Hk as Hk'. rewrite <- Hk'. apply E'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. 
  apply ev_inversion in H.
  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.


Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [| n' E' Heq ].
  inversion E' as [| n'' E'' Heq' ].
  apply E''.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [| n E Heq].
  inversion E as [| n' E' Heq'].
  inversion E'.
Qed.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
Search cons.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.


Lemma tst : forall n, 
  (exists k, n = Logic.double k) -> (exists k', S (S n) = Logic.double k').
Proof.
  intros n [k H].
  exists (S k).
  simpl.
  rewrite <- H.
  reflexivity.
Qed.


Lemma ev_Even_firsttry : forall n,
  ev n -> Logic.Even n.
Proof.
  unfold Logic.Even.
  intros n H.
  inversion H as [HEq | n' E HEq].
  - exists O. reflexivity.
  - apply tst.
    generalize dependent E. (* Prooving the same theorem *)
Abort.

Include Logic.

Lemma ev_Even : forall n, ev n -> Even n.
Proof.
  intros n E.
  induction E as [| n' E' IH ].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even E' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [| n' Hn' H ].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply H.
Qed.








Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros H'.
    induction H' as [ | | n m Hn Hn' Hm Hm'].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply Hn'.
      * apply Hm'.
  - intros H'.
    induction H' as [ | n Hn H ].
    + apply ev'_0.
    + apply (ev'_sum 2 n ev'_2 H).
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Hnm Hn.
  induction Hn as [| n' Hn' H].
  - simpl in Hnm. apply Hnm.
  - apply H. simpl in Hnm.
    remember (S (S (n' + m))) as k eqn:Hk.
    destruct Hnm as [| nm' Hnm'] eqn:E.
    + discriminate Hk.
    + injection Hk as Hk'.
      rewrite <- Hk'.
      apply Hnm'.
Qed.


Lemma es_sum : forall n m, 
  ev (n + m) -> (ev n /\ ev m) \/ (~(ev n) /\ ~(ev m)).
Proof.
  intros n m H.
  induction n as [| n' Hn ].
  - simpl in H.
    left. split.
    + apply ev_0.
    + apply H.
Abort.

Theorem ev_ev__ev1 : forall n m,
  ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [| n' Hn' H].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply H.
Qed.

Lemma tst1 : forall n, ev (n + n).
Proof.
  intros n.
  induction n as [| n' H'].
  - simpl. apply ev_0.
  - simpl. rewrite -> PeanoNat.Nat.add_comm. simpl. apply ev_SS. apply H'.
Qed.

Search (?a + (?b + ?c) = ?a + ?b + ?c).
Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  assert(H: ev (n + m + (n + p))). {
    apply (ev_ev__ev1 (n + m) (n + p) Hnm Hnp).
  }
  rewrite -> PeanoNat.Nat.add_assoc in H.
  rewrite -> PeanoNat.Nat.add_comm in H.
  rewrite -> (PeanoNat.Nat.add_comm (n + m) n) in H.
  rewrite -> PeanoNat.Nat.add_comm in H.
  rewrite -> (PeanoNat.Nat.add_assoc) in H.
  rewrite <- (PeanoNat.Nat.add_assoc) in H.
  apply (ev_ev__ev _ _ H (tst1 n)).
Qed.


Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
Notation "n <= m" := (le n m).

Theorem test_le1 : 3 <= 3.
Proof. apply le_n. Qed.

Theorem test_le2 : 3 <= 6.
Proof. apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 : (2 <= 1) -> 2 + 2 = 5.
Proof. intros H. inversion H. inversion H2. Qed.

Definition lt (n m : nat) := le (S n) m.
Notation "m < n" := (lt m n).

Theorem test_lt1 : 2 < 3.
Proof. unfold lt. apply le_n. Qed.


Lemma O_lowest : forall n, 0 <= n.
Proof.
  intros n.
  induction n as [| n' IH ].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Lemma O_split : forall a b, 
  0 = a + b -> a = 0 /\ b = 0.
Proof.
  intros a b H.
  destruct a as [| a'].
  - destruct b as [| b'].
    + split. reflexivity. reflexivity.
    + simpl in H. discriminate H.
  - simpl in H. discriminate H.
Qed.

Lemma m_le_mplus : forall m k, 
  m <= m + k.
Proof.
  intros m k.
  induction k as [| k' IH].
  - rewrite -> PeanoNat.Nat.add_comm. simpl. apply le_n.
  - rewrite -> PeanoNat.Nat.add_comm.
    simpl.
    apply le_S.
    rewrite -> PeanoNat.Nat.add_comm.
    apply IH.
Qed.

Lemma tst : forall m n, 
  m <= n <-> exists k, n = m + k.
Proof.
  intros m n.
  split.
  {
    intros Hmn.
    induction Hmn as [mn | m n Hmn' IH ].
    - exists O.
      rewrite -> PeanoNat.Nat.add_comm.
      reflexivity.
    - destruct IH as [k IH'].
      exists (S k).
      rewrite -> IH'.
      rewrite -> (PeanoNat.Nat.add_comm m (S k)).
      simpl.
      rewrite -> (PeanoNat.Nat.add_comm m k).
      reflexivity.
    }
    {
      intros [k He].
      rewrite -> He.
      apply m_le_mplus.
    }
Qed.

Lemma le_trans : forall m n o, 
  m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  destruct (tst m n) as [H1mn H2mn].
  destruct (tst n o) as [H1no H2no].
  destruct (H1mn Hmn) as [k1 E1].
  destruct (H1no Hno) as [k2 E2].
  rewrite -> E1 in E2.
  rewrite <- PeanoNat.Nat.add_assoc in E2.
  rewrite -> tst.
  exists (k1 + k2).
  apply E2.
Qed. 

Theorem O_le_n : forall n, 0 <= n.
Proof. apply O_lowest. Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Hnm.
  induction Hnm as [n | n m Hnm' IH].
  - apply le_n.
  - apply le_S.
    apply IH.
Qed.

Theorem n_lower_O_is_O: forall n, n <= 0 -> n = 0.
Proof.
  intros n H.
  remember 0 as o.
  destruct H as [k | x y Hxy].
  - rewrite -> Heqo.
    reflexivity.
  - discriminate Heqo.
Qed.

Theorem Sn_le_m__n_le_m : forall n m,
  S n <= m -> n <= m.
Proof.
  intros n m Hsnm.
  remember (S n) as sn.
  destruct Hsnm as [nm | n' m' Hnm ].
  - rewrite -> Heqsn.
    apply le_S.
    apply le_n.
  - apply le_S.
    destruct (tst n n') as [Htstl Htstr].
    assert (G: n <= n'). {
      apply Htstr.
      exists 1.
      rewrite -> PeanoNat.Nat.add_comm.
      simpl.
      apply Heqsn.
    }
    apply (le_trans n n' m').
    apply G.
    apply Hnm.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m Hsnsm.
  rewrite -> tst.
  assert (H: exists k : nat, m = n + k). {
    destruct (tst (S n) (S m)) as [Htstl Htstr].
    simpl in Htstl.
    destruct (Htstl Hsnsm) as [k G].
    injection G as G'.
    exists k.
    apply G'.
  }
  apply H.
Qed.

Theorem Sn_le_Sm__n_le_m' : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  remember (S n) as sn eqn:Esn.
  remember (S m) as sm eqn:Esm.
  induction H as [n' | n' m' H' IH].
  - rewrite -> Esn in Esm.
    injection Esm as G.
    rewrite -> G.
    apply (le_n m).
  - injection Esm as G.
    rewrite -> G in H'.
    rewrite -> Esn in H'.
    apply Sn_le_m__n_le_m.
    apply H'.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ m <= n.
Proof.
  intros n.
  induction n as [| n' IHn ].
  - unfold lt.
    intros m.
    induction m as [| m' IHm].
    + right. apply le_n.
    + destruct IHm as [IHml | IHmr].
      * left. apply le_S. apply IHml.
      * assert (G: m' = 0). {apply n_lower_O_is_O. apply IHmr. }
        left.
        rewrite -> G.
        apply le_n.
  - unfold lt.
    intros m.
    induction m as [| m' IHm].
    + right. apply O_lowest.
    + destruct IHm as [IHml | IHmr].
      * left. 
        apply le_S in IHml.
        apply IHml.
      * unfold lt in IHn.
        destruct (IHn m') as [IHnl | IHnr].
        -- left. apply n_le_m__Sn_le_Sm. apply IHnl.
        -- right. apply n_le_m__Sn_le_Sm. apply IHnr.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. apply m_le_mplus. Qed. 

Theorem plus_le : forall a b m,
  a + b <= m -> a <= m /\ b <= m.
Proof.
  intros a b m H.
  assert (G: exists k, m = a + b + k). {
    destruct (tst (a + b) m) as [Tl Tr].
    apply (Tl H).
  }
  split.
  - destruct (tst a m) as [Tl Tr].
    apply Tr.
    destruct G as [k Hd].
    exists (b + k).
    rewrite -> PeanoNat.Nat.add_assoc.
    apply Hd.
  - destruct (tst b m) as [Tl Tr].
    apply Tr.
    destruct G as [k Hd].
    exists (a + k).
    rewrite -> PeanoNat.Nat.add_assoc.
    rewrite -> (PeanoNat.Nat.add_comm b a).
    apply Hd.
Qed.

Theorem t: forall n m, n < S m -> S n <= m. 
Proof.
  unfold lt.
  Admitted.

Theorem le_symm_fw : forall n m p, n + m <= n + p -> m <= p.
Proof.
  intros n.
  induction n as [| n' IH ].
  - simpl. intros m p H. apply H.
  - intros m p. simpl. intros H. 
    apply (Sn_le_Sm__n_le_m (n' + m) (n' + p)) in H.
    apply IH.
    apply H.
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n.
  induction n as [| n' IH ].
  - simpl. intros m p q H.
    left. apply O_lowest.
  - simpl. intros m p q H.
    assert (G' : n' <= p \/ S m <= q). {
      apply IH.
      rewrite -> (PeanoNat.Nat.add_comm n' (S m)).
      simpl.
      rewrite -> (PeanoNat.Nat.add_comm m n').
      apply H.
    }
    destruct G' as [G'l | G'r].
    + destruct G'l as [n' | n' p HH].
      * assert (H0: S m <= q). {
          apply (le_symm_fw n').
          rewrite -> (PeanoNat.Nat.add_comm n' (S m)).
          simpl.
          rewrite -> (PeanoNat.Nat.add_comm m n').
          apply H.
        }
        right.
        apply Sn_le_m__n_le_m.
        apply H0.
      * left.
        apply n_le_m__Sn_le_Sm.
        apply HH.
    + right. apply Sn_le_m__n_le_m. apply G'r.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m -> p + n <= p + m.
Proof.
  intros n m p.
  induction p as [| p' IH ].
  - simpl. intros H. apply H.
  - intros H. simpl. 
    apply n_le_m__Sn_le_Sm.
    apply IH.
    apply H.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m -> n + p <= m + p.
Proof.
  intros n m p.
  rewrite -> (PeanoNat.Nat.add_comm n p).
  rewrite -> (PeanoNat.Nat.add_comm m p).
  apply plus_le_compat_l.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p.
  induction p as [| p' IH].
  - intros H. rewrite -> (PeanoNat.Nat.add_comm m 0). simpl. apply H.
  - intros H.
    rewrite -> (PeanoNat.Nat.add_comm m (S p')).
    simpl.
    apply le_S.
    rewrite -> (PeanoNat.Nat.add_comm p' m).
    apply IH.
    apply H.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n m.
  unfold lt.
  apply Sn_le_m__n_le_m.
Qed.


Lemma less_one: forall a b,  S a <= b -> 1 <= b.
Proof.
  intros a b.
  induction a as [| a' IH ].
  - intros H. apply H.
  - intros H. 
    apply Sn_le_m__n_le_m in H.
    apply IH.
    apply H.
Qed.

Lemma nothing_less_O : forall n, 
  S n <= 0 -> False.
Proof.
  intros n H.
  remember (S n) as k.
  remember 0 as o.
  destruct H as [n' | n' o'].
  - rewrite -> Heqo in Heqk.
    discriminate Heqk.
  - discriminate Heqo.
Qed.

Theorem plus_lt : forall a b m,
  a + b < m -> a < m /\ b < m.
Proof.
  intros a.
  unfold lt.
  induction a as [| a' IH ].
  - intros b m H.
    simpl in H.
    split.
    + apply (less_one b). apply H.
    + apply H.
  - intros b m H.
    destruct m as [| m'].
    + exfalso.
      apply (nothing_less_O (S a' + b) H).
    + destruct m' as [| m''].
      * apply Sn_le_Sm__n_le_m' in H.
        simpl in H.
        exfalso.
        apply (nothing_less_O (a' + b) H).
      * apply Sn_le_Sm__n_le_m' in H.
        simpl in H.
        destruct (IH b (S m'') H) as [IHl IHr].
        split.
        -- apply n_le_m__Sn_le_Sm.
           apply IHl.
        -- apply le_S.
           apply IHr.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n.
  induction n as [| n' IHn ].
  - intros m H. apply O_lowest.
  - destruct m as [| m'].
    + intros H.
      simpl in H. discriminate H.
    + intros H. simpl in H.
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      apply H.
Qed.

Lemma leb_refl : forall n,
  n <=? n = true.
Proof.
  intros n.
  induction n as [| n' IH ].
  - reflexivity.
  - simpl. apply IH.
Qed.

Lemma leb_s_rev : forall n m,
  S n <=? m = true -> n <=? m = true.
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [| m' IHm ].
  - intros n H. simpl in H. discriminate H.
  - intros n H. simpl in H.
    destruct n as [| n'] eqn: En.
    + reflexivity.
    + simpl.
      apply (IHm n').
      apply H.
Qed.

Lemma leb_s : forall n m,
  n <=? m = true -> n <=? S m = true.
Proof.
  intros n m H.
  generalize dependent m.
  induction n as [| n' IHn ].
  - reflexivity.
  - destruct m as [| m'] eqn: Em.
    + intros H. simpl in H. discriminate H.
    + simpl. intros H.
      apply (IHn m').
      apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> n <=? m = true.
Proof.
  intros n m H.
  induction m as [| m' IHm ].
  - apply n_lower_O_is_O in H.
    rewrite -> H.
    reflexivity.
  - remember (S m') as sm' eqn:Hsm.
    destruct H as [n | n m H'].
    + apply leb_refl.
    + injection Hsm as Hsm'.
      rewrite <- Hsm' in IHm.
      apply IHm in H'.
      apply leb_s.
      apply H'.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Hnm Hmo.
  rewrite -> leb_iff in Hnm.
  rewrite -> leb_iff in Hmo.
  rewrite -> leb_iff.
  apply (le_trans n m o Hnm Hmo).
Qed.

End Playground.


Inductive total_relation : nat -> nat -> Prop :=
  | total n m : total_relation n m.

Example total_ex: total_relation 9 666.
Proof. apply total. Qed.


Inductive empty_relation : nat -> nat -> Prop :=.
Example empty_ex: empty_relation 1 1.
Proof. Abort.


Module R.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o )                : R (S m) n (S o)
  | c3 m n o (H : R m n o )                : R m (S n) (S o)
(*  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
    | c5 m n o (H : R m n o )                : R n m o
*)
.

Lemma exr1: R 1 1 2.
Proof. apply c3. apply c2. apply c1. Qed. 

Lemma exr2: R 2 2 6.
Proof. apply c3. apply c2. Abort.

Search (nat -> nat -> nat).
Definition fR : nat -> nat -> nat := PeanoNat.Nat.add.


Theorem R_equiv_fR : forall m n o, 
  R m n o <-> fR m n = o.
Proof.
  intros m n o.
  split.
  - intros H.
    induction H as [| m n o H2 IH2 | m n o H3 IH3 ].
    + reflexivity.
    + simpl. rewrite -> IH2. reflexivity.
    + unfold fR. 
      unfold fR in IH3. 
      rewrite -> PeanoNat.Nat.add_comm. 
      simpl. 
      rewrite -> PeanoNat.Nat.add_comm. 
      rewrite -> IH3. 
      reflexivity.
  - intros H.
    generalize dependent n.
    generalize dependent o.
    induction m as [| m' IHm ].
    + intros o n H.
      simpl in H.
      rewrite -> H.
      assert (R_0_n_n : forall n, R 0 n n). {
        intros k.
        induction k as [| k' IHk ].
        - apply c1.
        - apply c3. apply IHk.
      }
      apply R_0_n_n.
    + intros o n H.
      simpl in H.
      unfold fR in IHm.
      unfold fR in H.
      destruct o as [| o'].
      * discriminate H.
      * apply c2.
        apply IHm.
        injection H as H'.
        apply H'.
Qed.

End R.



Module Sublist.

Inductive subseq : list nat -> list nat -> Prop :=
  | empty l                     : subseq nil        l
  | add   a s l (H: subseq s l) : subseq (cons a s) (cons a l)
  | add_l a s l (H: subseq s l) : subseq s          (cons a l)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l.
  induction l as [| hl tl IHl].
  - apply empty.
  - apply (add hl). apply IHl.
Qed.

Theorem subseq_app : forall (s l l' : list nat),
  subseq s l ->
  subseq s (l ++ l').
Proof.
  intros s l l' H.
  generalize dependent s.
  generalize dependent l'.
  induction l as [| hl tl IHl ].
  - intros l' s H. simpl.
    remember [] as k eqn:Ek. 
    destruct H as [l | a s l | a s l].
    + apply empty.
    + discriminate Ek.
    + discriminate Ek.
  - remember (hl :: tl) as k eqn:Ek.
    intros l' s H.
    rewrite -> Ek.
    simpl.
    destruct H as [lh | ah sh lh H' | ah sh lh H'].
    + apply empty.
    + 
      injection Ek as Ea Es.
      rewrite -> Ea.
      apply add.
      apply IHl.
      rewrite <- Es.
      apply H'.
    + injection Ek as Ea Es.
      apply add_l.
      apply IHl.
      rewrite <- Es.
      apply H'.
Qed.


Theorem subseq_trans : ∀ (l1 l2 l3 : list nat),
  subseq l1 l2 →
  subseq l2 l3 →
  subseq l1 l3.
Proof.
  (* FILL IN HERE *) Admitted.

End Sublist.




End IndProp.