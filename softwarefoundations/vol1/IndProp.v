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

Notation "a $ b" := (subseq a b)
                    (at level 60).

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

Lemma ht_subset_then_t_subset : forall a s l, 
  subseq (a :: s) l -> subseq s l.
Proof.
  intros a s l H.
  remember (a :: s) as k eqn:Ek.
  induction H as [l | a' s' l' H' IH | a' s' l' H' IH].
  - discriminate Ek.
  - injection Ek as Eka Eks.
    apply add_l.
    rewrite -> Eks in H'.
    apply H'.
  - apply add_l.
    apply IH.
    apply Ek.
Qed.

Lemma false_sublist: forall s, subseq s [ ] -> s = [ ].
Proof.
  intros s H.
  remember [ ] as k eqn:Ek.
  destruct H as [ l | a s' l | a s' l].
  - rewrite -> Ek. reflexivity.
  - discriminate Ek.
  - discriminate Ek.
Qed.

Lemma destruct_second_cons : forall a h t, 
  subseq a (h :: t) -> 
  (exists at', a = h :: at' /\ subseq at' t)
  \/
  subseq a t.
Proof.
  intros a h t H.
  remember (h :: t) as k eqn:Ek.
  destruct a as [| ah at' ] eqn:Ea.
  - right. apply empty.
  - destruct H as [l | hH sH lH H' | hH sH lH H' ].
    + right. apply empty.
    + left.
      exists sH.
      injection Ek as Ek1 Ek2.
      split.
      * rewrite -> Ek1. reflexivity.
      * rewrite <- Ek2. apply H'.
    + right.
      injection Ek as Ek1 Ek2.
      rewrite <- Ek2.
      apply H'.
Qed.


Lemma elim_same_head : forall h a b, (h :: a) $ (h :: b) -> a $ b.
Proof.
  intros h a b H.
  remember (h :: a) as ra eqn:Era.
  remember (h :: b) as rb eqn:Erb.
  induction H as [l | h' s l H' IH | h' s l H' IH].
  - discriminate Era.
  - injection Era as Era1 Era2.
    injection Erb as Erb1 Erb2.
    rewrite <- Erb2.
    rewrite <- Era2.
    apply H'.
  - rewrite -> Era in H'.
    injection Erb as Erb1 Erb2.
    rewrite -> Erb2 in H'.
    apply ht_subset_then_t_subset in H'.
    apply H'.
Qed.


Theorem subseq_trans_h2: forall a b c,
  a $ b -> b $ c -> a $ c.
Proof.
  intros a b c H1 H2.
  generalize dependent a.
  induction H2 as [l | h s l H2' IH | h s l H2' IH ].
  - intros a H1.
    apply false_sublist in H1.
    rewrite -> H1.
    apply empty.
  - intros a H1.
    assert (G: (exists at', a = h :: at' /\ subseq at' s) \/ subseq a s). {
      apply destruct_second_cons.
      apply H1.
    }
    destruct G as [[atail [HAeq Hatail]] | Has ].
    + rewrite -> HAeq.
      apply add.
      rewrite -> HAeq in H1.
      apply elim_same_head in H1.
      apply IH.
      apply H1.
    + apply add_l.
      apply IH.
      apply Has.
  - intros a H1.
    apply add_l.
    apply IH.
    apply H1.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  apply subseq_trans_h2.
Qed.

End Sublist.

Inductive R : nat -> list nat -> Prop :=
  | c1                    : R 0     []
  | c2 n l (H: R n     l) : R (S n) (n :: l)
  | c3 n l (H: R (S n) l) : R n     l.

(* Which of the following propositions are provable? *)
Theorem tr1: R 2 [1;0].
Proof. apply c2. apply c2. apply c1. Qed.

Theorem tr2: R 1 [1;2;1;0].
Proof. apply c3. apply c2. apply c3. apply c3. apply c2. apply c2. apply c2. apply c1. Qed.

Theorem tr3: R 6 [3;2;1;0].
Proof. Abort.


Module RegExp.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).


(*
    The expression EmptySet does not match any string.
    The expression EmptyStr matches the empty string [].
    The expression Char x matches the one-character string [x].
    If re1 matches s1, and re2 matches s2, then App re1 re2 matches s1 ++ s2.
    If at least one of re1 and re2 matches s, then Union re1 re2 matches s.
    Finally, if we can write some string s as the concatenation of a sequence of 
      strings s = s_1 ++ ... ++ s_k, and the expression re matches each one of the 
      strings s_i, then Star re matches s.
    In particular, the sequence of strings may be empty, so Star re always matches 
      the empty string [] no matter what re is.
*)
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2] _).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. 
(*  remember ([1; 2]) as k eqn:Ek.

  destruct H as [| c | s1 re1 s2 re2 h1 h2 | s1 re1 re2 h1 | re1 s2 re2 h2 | re | s1s2 h1 h2] eqn:E.
  - 
*)
  inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) : reg_exp T:=
  match l with
  | [ ]     => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.


Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Search (?s ++ [] = ?s).
Lemma MStar1 : forall T s (re : reg_exp T) ,
    s =~ re -> s =~ Star re.
Proof.
  intros T s re H.
  assert (G: s ++ [] =~ Star re). {
   apply (MStarApp s [] re).
   - apply H.
   - apply MStar0.
  }
  rewrite -> List.app_nil_r in G.
  apply G.
Qed.


Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s.
  unfold not.
  intros H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H as [Hl | Hr].
  - apply (MUnionL).
    apply Hl.
  - apply (MUnionR).
    apply Hr.
Qed.

(* 
  The next lemma is stated in terms of the fold function from the Poly chapter: 
  If ss : list (list T) represents a sequence of strings s1, ..., sn, then fold 
  app ss [] is the result of concatenating them all together.
*)

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y): Y :=
  match l with
  | nil    => b
  | h :: t => f h (fold f t b)
  end.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold (@app T) ss [] =~ Star re.
Proof.
  intros T ss.
  induction ss as [| h t IH].
  - simpl. intros re H. apply MStar0.
  - simpl. intros re H.
    apply (MStarApp h (fold (@app T) t [ ])).
    + apply H. left. reflexivity.
    + apply IH.
      intros l H'.
      apply H.
      right.
      apply H'.
Qed.

Theorem reg_exp_of_list_refl: forall T (s: list T),
  s =~ reg_exp_of_list s.
Proof.
  intros T s.
  induction s as [| h t IH ].
  - simpl. apply MEmpty.
  - simpl.
    assert (G: h :: t = [h] ++ t). {
      reflexivity.
    }
    rewrite -> G.
    apply MApp.
    + apply MChar.
    + apply IH.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2.
  split.
  - generalize dependent s1.
    induction s2 as [| h t IH ].
    + intros s1 H.
      simpl in H. 
      inversion H.
      reflexivity.
    + intros s1 H.
      simpl in H.
      inversion H. (* Only one branch with App *)
      inversion H3.
      simpl.
      rewrite -> (IH s2 H4).
      reflexivity.
  - intros H.
    rewrite <- H.
    apply reg_exp_of_list_refl.
Qed.


Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet      => []
  | EmptyStr      => []
  | Char x        => [x]
  | App re1 re2   => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re       => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x H Hin.
  induction H as [| c 
                  | s1 re1 s2 re2 H1 IH1 H2 IH2
                  | s1 re1 re2 H1 IH
                  | re1 s2 re2 H2 IH
                  | re
                  | s1 s2 re H1 IH1 H2 IH2 ].
  - (* MEmpty  *)
    simpl in Hin. exfalso. apply Hin.
  - (* MChar *)
    simpl. simpl in Hin. apply Hin.
  - (* MApp *)
    simpl. rewrite In_app_iff. 
    rewrite In_app_iff in Hin. 
    destruct Hin as [Hinl | Hinr]. 
    + left.  apply IH1. apply Hinl.
    + right. apply IH2. apply Hinr.
  - (* MUnionL *)
    simpl. rewrite In_app_iff. left. apply IH. apply Hin.
  - (* MUnionR *)
    simpl. rewrite In_app_iff. right. apply IH. apply Hin.
  - (* MStar0 *)
    simpl in Hin. exfalso. apply Hin.
  - (* MStarApp *)
    rewrite In_app_iff in Hin. 
    destruct Hin as [Hinl | Hinr].
    + simpl. apply IH1. apply Hinl.
    + simpl. apply IH2. apply Hinr.
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet      => false
  | EmptyStr      => true
  | Char x        => true
  | App re1 re2   => re_not_empty re1 && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re       => true
  end.

Search (orb ?a ?b = orb ?b ?a).

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  - intros [s H].
    induction H as [| c 
                | s1 re1 s2 re2 H1 IH1 H2 IH2
                | s1 re1 re2 H1 IH
                | re1 s2 re2 H2 IH
                | re
                | s1 s2 re H1 IH1 H2 IH2 ].
    + (* MEmpty  *)
      simpl. reflexivity.
    + (* MChar *)
      simpl. reflexivity.
    + (* MApp *)
      simpl. rewrite -> IH1. rewrite -> IH2. reflexivity.
    + (* MUnionL *)
      simpl. rewrite -> IH. reflexivity.
    + (* MUnionR *)
      simpl. rewrite -> IH. rewrite Bool.orb_comm. reflexivity.
    + (* MStar0 *)
      reflexivity. 
    + (* MStarApp *)
      reflexivity.
  - intros H.
    induction re as [|
                    | c
                    | re1 IH1 re2 IH2
                    | re1 IH1 re2 IH2
                    | r IH ].
    + (* EmptySet *)
      simpl in H. discriminate H.
    + (* EmptyStr *)
      simpl in H. exists [ ]. apply MEmpty.
    + (* Char (c : T) *)
      exists [c]. apply MChar.
    + (* App (r1 r2 : reg_exp T) *)
      simpl in H.
      destruct (re_not_empty re1).
      -- destruct (re_not_empty re2).
         ++ simpl in H.
            destruct (IH1 H) as [s1 H'1].
            destruct (IH2 H) as [s2 H'2].
            exists (s1 ++ s2).
            apply (MApp _ _ _ _ H'1 H'2).
         ++ discriminate H.
      -- discriminate H.
    + (* Union (r1 r2 : reg_exp T) *)
      simpl in H.
      destruct (re_not_empty re1).
      -- destruct (IH1 H) as [s H'].
         exists s.
         apply (MUnionL _ _ _ H').
      -- destruct (re_not_empty re2).
         ++ destruct (IH2 H) as [s H'].
            exists s.
            apply (MUnionR _ _ _ H').
         ++ discriminate H.
    + (* Star (r : reg_exp T). *)
      exists [].
      apply MStar0.
Qed.




Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| h t H ].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.


Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re' eqn: Ere'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Ere' as Heqre''. intros s H. apply H.
  - (* MStarApp *)
    injection Ere' as Heqre''.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.


Lemma Star_lemm: forall T (s1 s2 : list T) re,
  s1 =~ re -> s2 =~ Star re -> (s1 ++ s2) =~ Star re.
Proof.
  intros T s1 s2 re H1 H2.
  apply (MStarApp s1 _ _ H1) in H2.
  apply H2.
Qed.

Search (?l ++ [] = ?l).

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T), (s = fold (@app T) ss []) /\ (forall s', In s' ss -> s' =~ re).
Proof.
  intros T s re H.
  remember (Star re) as k eqn:Ek.
  induction H as [| c 
                  | s1 re1 s2 re2 H1 IH1 H2 IH2
                  | s1 re1 re2 H1 IH
                  | re1 s2 re2 H2 IH
                  | re1
                  | s1 s2 re1 H1 IH1 H2 IH2 ].
  - discriminate Ek.
  - discriminate Ek.
  - discriminate Ek.
  - discriminate Ek.
  - discriminate Ek.
  - exists [].
    simpl.
    split.
    + reflexivity.
    + intros s' F. exfalso. apply F.
  - destruct (IH2 Ek) as [ss [H'1 H'2]]. (* Get list of matched strings from Inductive Hypo *)
    exists ([s1] ++ ss).
    split.
    + simpl.
      rewrite <- H'1.
      reflexivity.
    + intros s'.
      simpl. 
      intros G.
      destruct G as [G1 | G2].
      * rewrite <- G1.
        injection Ek as Ek'.
        rewrite <- Ek'.
        apply H1.
      * apply H'2.
        apply G2.
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_constant_ge_1 : forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
Admitted.
(*
  intros T re. induction re.
  - (* EmptySet *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.
*)

Lemma pumping_constant_0_false : forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.


Search (?l ++ [] = ?l).
Search (length (?s1 ++ ?s2) = length (?s1) + length (?s2)).
Search (?a + ?b <= ?c + ?d -> ?a <= ?c \/ ?b <= ?d).
Search (?a + ?b <= ?c -> ?a <= ?c /\ ?b <= ?c).
Search (?a <= ?b + ?c -> ?a <= ?b /\ ?a <= ?c).
Search (plus_le).
Search (le_plus).
Lemma plus_le: forall a b c, a + b <= c -> a <= c /\ b <= c.
Proof. Admitted.

Lemma le_plus: forall a b c, a <= b + c -> a <= b /\ a <= c.
Proof. Admitted.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    exists [].
    simpl in H.
    inversion H.
    inversion H1.
  - (* MApp *)
    simpl.
    intros H.
    rewrite -> List.app_length in H.
    destruct (PeanoNat.Nat.add_le_cases _ _ _ _ H) as [Hl | Hr ].
    + destruct (IH1 Hl) as [s2' [s3' [s4' [G1 [G2 G3]]]]].
      exists s2'.
      exists s3'.
      exists (s4' ++ s2).
      split.
      * rewrite -> G1.
        rewrite <- app_assoc.
        rewrite <- app_assoc.
        reflexivity.
      * split.
        -- apply G2.
        -- intros m.
           rewrite -> app_assoc.
           rewrite -> app_assoc.
           rewrite <- (app_assoc _ s2' (napp m s3') s4').
           apply MApp.
           ++ apply (G3 m).
           ++ apply Hmatch2.
    + destruct (IH2 Hr) as [s2' [s3' [s4' [G1 [G2 G3]]]]].
      exists (s1 ++ s2').
      exists s3'.
      exists s4'.
      split.
      * rewrite -> G1.
        rewrite <- app_assoc.
        reflexivity.
      * split.
        -- apply G2.
        -- intros m.
           rewrite <- app_assoc.
           apply MApp.
           ++ apply Hmatch1.
           ++ apply (G3 m).
  - (* MUnionL *) 
    simpl.
    intros H.
    destruct (plus_le _ _ _ H) as [Hre1 Hre2].
    destruct (IH Hre1) as [s2' [s3' [s4' [G1 [G2 G3]]]]].
    exists s2'.
    exists s3'.
    exists s4'.
    split.
    + apply G1.
    + split.
      * apply G2.
      * intros m.
        apply MUnionL.
        apply G3.
  - (* MUnionR *)
    simpl.
    intros H.
    destruct (plus_le _ _ _ H) as [Hre1 Hre2].
    destruct (IH Hre2) as [s2' [s3' [s4' [G1 [G2 G3]]]]].
    exists s2'.
    exists s3'.
    exists s4'.
    split.
    + apply G1.
    + split.
      * apply G2.
      * intros m.
        apply MUnionR.
        apply G3.
  - (* MStar0 *)
    intros H.
    simpl in H.
    destruct (pumping_constant_ge_1 T re).
    + inversion H.
    + inversion H.
  - (* MStarApp *)
    simpl.
    intros H.
    rewrite -> List.app_length in H.
    destruct (le_plus _ _ _ H) as [Hl Hr ].
    destruct (IH1 Hl) as [s2' [s3' [s4' [G1 [G2 G3]]]]].
    destruct (IH2 Hr) as [s2'2 [s3'2 [s4'2 [G12 [G22 G32]]]]].
    exists s2'.
    exists s3'.
    exists (s4' ++ s2).
    split.
    + rewrite -> G1.
      rewrite <- (app_assoc _).
      rewrite <- (app_assoc _).
      reflexivity.
    + split.
      * apply G2.
      * intros m.
        rewrite -> (app_assoc _).
        rewrite -> (app_assoc _).
        rewrite <- (app_assoc _ s2').
        apply MStarApp.
        -- apply (G3 m).
        -- apply Hmatch2.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\ s2 <> [] 
      /\ length s1 + length s2 <= pumping_constant re /\ forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
Admitted.


End Pumping.

End RegExp.


Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  destruct H as [p | p].
  - split.
    + intros P'. reflexivity.
    + intros T. apply p.
  - split.
    + intros P'. exfalso. apply (p P').
    + intros F. discriminate F.
Qed.

Lemma eqb_eq : forall m n, n = m <-> (n =? m) = true.
Proof.
  intros m n.
  split.
  - intros H.
    rewrite -> H.
    assert(G: forall n, (n =? n) = true). {
      intros k.
      induction k as [| k' IH].
      - reflexivity.
      - simpl. rewrite -> IH. reflexivity.
    }
    apply G. 
  - generalize dependent m.
    induction n as [| n' IH].
    + destruct m as [| m'].
      * simpl. intros H. reflexivity.
      * simpl. intros H. discriminate H.
    + destruct m as [| m'].
      * simpl. intros H. discriminate H.
      * simpl. intros H. rewrite -> (IH m' H). reflexivity.
Qed.


Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.


Fixpoint filter {X: Type} (test: X -> bool) (l: list X) : list X :=
  match l with
  | []     => []
  | h :: t =>
    if test h 
    then h :: (filter test t)
    else filter test t
  end.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.


Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l H.
  induction l as [| h t IH ].
  - simpl in H. simpl. unfold not. intros F. apply F.
  - simpl.
    simpl in H.
    destruct (eqbP n h) as [Heq | Heq].
    + simpl in H.
      discriminate H.
    + simpl in H.
      apply IH in H.
      unfold not.
      intros G.
      destruct G as [G1 | G2].
      * apply Heq.
        symmetry.
        apply G1.
      * apply H.
        apply G2.
Qed.


Module Stutter.
Inductive nostutter {X:Type} : list X -> Prop :=
  | empty : nostutter nil
  | one x : nostutter [x]
  | add n x t (Hneq : n <> x) (Hh : nostutter (x :: t)) : nostutter (n :: x :: t)
.

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; auto. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.
End Stutter.


Module InOrderMerged.
Inductive in_order_merged {X:Type} : list X -> list X -> list X -> Prop :=
  | empty : in_order_merged nil nil nil
  | addl n l1 l2 lr (H: in_order_merged l1 l2 lr) : in_order_merged (n :: l1) l2 (n :: lr)
  | addr n l1 l2 lr (H: in_order_merged l1 l2 lr) : in_order_merged l1 (n :: l2) (n :: lr)
.

Example ex1 : in_order_merged [1;6;2] [4;3] [1;4;6;2;3].
Proof. apply addl. apply addr. apply addl. apply addl. apply addr. apply empty. Qed.

Fixpoint elem_of (l: list nat) (x : nat) : bool :=
  match l with
  | nil => false
  | cons h t => if h =? x then true else elem_of t x
  end.

Lemma same_start_list: forall T (h : T) (t t': list T), t = t' -> h :: t = h :: t'.
Proof.
  intros T h t t' H.
  rewrite -> H.
  reflexivity.
Qed.

Lemma add_false_simpl: forall P, (False \/ P) -> P.
Proof.
  intros P H.
  destruct H as [l | r].
  - exfalso. apply l.
  - apply r.
Qed.


Lemma inP : forall (x : nat) (l : list nat), 
  reflect (In x l) (elem_of l x).
Proof.
  intros x l.
  induction l as [| h t H].
  - simpl. apply ReflectF. unfold not. intros F. apply F.
  - simpl. 
    destruct (eqbP h x) as [Hhx|Hhx].
    + apply ReflectT.
      left. apply Hhx.
    + unfold not in Hhx.
      destruct H.
      * apply ReflectT. right. apply H.
      * apply ReflectF. unfold not.
        intros HF.
        destruct HF as [HFl|HFr].
        -- apply Hhx. apply HFl.
        -- apply H. apply HFr.
Qed.

Lemma neg_app: forall A B, (~ (A \/ B)) <-> ~A /\ ~B.
Proof.
  intros A B.
  split.
  * intros H.
    split.
    - unfold not in H.
      unfold not.
      intros AH.
      apply H.
      apply (or_intro_l A _ AH).
    - unfold not in H.
      unfold not.
      intros BH.
      apply H.
      apply (or_intro_r A B BH).
  * intros [Hl Hr].
    unfold not.
    intros Hor.
    destruct Hor as [Horl | Horr].
    - apply Hl. apply Horl.
    - apply Hr. apply Horr.
Qed.

Theorem sum_nas_no_item: forall A (x: A) l1 l2 lr, 
  in_order_merged l1 l2 lr -> (~ In x l1 /\ ~ In x l2 ) -> (~ (In x lr)).
Proof.
  intros A x l1 l2 lr H1 H2.
  induction H1 as [| n l1' l2' lr' H1' IH| n l1' l2' lr' H1' IH].
  - destruct H2 as [H2l H2r].
    apply H2l.
  - simpl. apply neg_app.
    simpl in H2. rewrite -> neg_app in H2.
    destruct H2 as [[Hneq Hxl1] Hxl2].
    split.
    + apply Hneq.
    + apply IH.
      split.
      * apply Hxl1.
      * apply Hxl2.
  - simpl. apply neg_app.
    simpl in H2. rewrite -> neg_app in H2.
    destruct H2 as [Hxl1 [Hneq Hxl2]].
    split.
    + apply Hneq.
    + apply IH.
      split.
      * apply Hxl1.
      * apply Hxl2.
Qed.

Lemma elem_of_h: forall h t, 
  elem_of (h :: t) h = true.
Proof.
  intros h t.
  simpl.
  destruct (eqbP h h) as [Hr | Hr].
  - reflexivity.
  - exfalso. apply Hr. reflexivity.
Qed.

Lemma n_eq_n: forall n, n =? n = true.
Proof.
  intros n.
  destruct (eqbP n n) as [Hl | Hr].
  - reflexivity.
  - exfalso. apply Hr. reflexivity.
Qed.

Lemma if_with_same_res: forall A (b : bool) (r: A), (if b then r else r) = r.
Proof.
  intros A b r.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Lemma add_existed: forall n l, 
  In n l -> (forall x, elem_of (n :: l) x = elem_of l x).
Proof.
  intros n l H x.
  simpl.
  destruct (eqbP n x) as [Hl | Hr].
  - rewrite <- Hl.
    destruct (inP n l) as [Hl' | Hr'].
    + reflexivity.
    + exfalso. apply Hr'. apply H.
  - reflexivity.
Qed.

Lemma filter_lemm: forall n l m, 
  In n l -> filter (elem_of (n :: l)) m = filter (elem_of l) m.
Proof.
  intros n l m H.
  simpl.
  induction m as [| mh mt IH].
  - reflexivity.
  - simpl.
    destruct (eqbP n mh) as [Hl | Hr].
    + rewrite <- Hl.
      destruct (inP n l) as [Hl' | Hr'].
      * rewrite <- IH. reflexivity.
      * exfalso. apply Hr'. apply H.
    + rewrite -> IH. reflexivity.
Qed.
  
Lemma tst: forall n p l, ~ In n l -> filter (fun x : nat => if n =? x then true else p x) l = filter p l.
Proof.
  intros n p l H.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    destruct (eqbP n h).
    + exfalso. apply H. simpl. left. rewrite -> H0. reflexivity.
    + assert (G: ~ In n t). {
        simpl in H.
        apply neg_app in H.
        destruct H as [Hl Hr].
        apply Hr.
      }
      rewrite -> (IH G).
      reflexivity.
Qed.

Lemma exclusion_rev: forall A (l1 l2 : list A), 
  (forall x, In x l1 -> ~(In x l2)) -> (forall x, In x l2 -> ~(In x l1)).
Proof.
  intros A l1 l2 H x H2.
  unfold not.
  intros G.
  apply (H x G).
  apply H2.
Qed.

Theorem filter_preserve_ord: forall l1 l2 lr, 
  in_order_merged l1 l2 lr -> (forall x, In x l1 -> ~(In x l2)) -> filter (elem_of l1) lr = l1.
Proof.
  intros l1 l2 lr H Hexcl.
  induction H as [| n l1' l2' lr' H' IH| n l1' l2' lr' H' IH].
  - reflexivity.
  - destruct (inP n l1') as [Hl | Hr].
    + rewrite -> (filter_lemm _ _ _ Hl).
      simpl.
      assert (G: elem_of l1' n = true). {
        destruct (inP n l1').
        - reflexivity.
        - exfalso. apply H. apply Hl.
      }
      rewrite -> G.
      assert (G': forall x : nat, In x l1' -> ~ In x l2'). {
        intros x HIn.
        apply Hexcl.
        simpl. right. apply HIn.
      }
      rewrite -> (IH G').
      reflexivity.
    + simpl.
      rewrite -> n_eq_n.
      assert (Hnl2': ~ In n l2'). {
        apply Hexcl.
        simpl. left. reflexivity.
      }
      assert (Hnlr': ~ In n lr'). {
        apply (sum_nas_no_item _ _ _ _ _ H').
        split. apply Hr. apply Hnl2'.
      }
      rewrite -> (tst n (elem_of l1') lr' Hnlr').
      assert (G: forall x : nat, In x l1' -> ~ In x l2'). {
        intros x H.
        apply Hexcl.
        simpl.
        right. apply H.
      }
      rewrite -> (IH G).
      reflexivity.
  - simpl.
    destruct (inP n l1') as [Hl | Hr].
    + apply Hexcl in Hl.
      simpl in Hl.
      rewrite -> neg_app in Hl.
      destruct Hl as [Hll Hlr].
      exfalso. apply Hll. reflexivity.
    + assert (G: forall x : nat, In x l1' -> ~ In x l2'). {
        intros x H.
        apply Hexcl in H.
        simpl in H.
        rewrite -> neg_app in H.
        destruct H as [Hl' Hr'].
        apply Hr'.
      }
      rewrite -> (IH G).
      reflexivity.
Qed.

End InOrderMerged.

(*
A different way to characterize the behavior of filter goes like this: 
  Among all subsequences of l with the property that test 
  evaluates to true on all their members, filter test l is 
  the longest. Formalize this claim and prove it. 
*)


Module Pal.

Inductive pal {X:Type} : list X -> Prop :=
  | empty : pal nil 
  | one (c : X) : pal [c]
  | step (c: X) (l: list X) (H: pal l): pal (c :: l ++ [c])
.

Example pal_e1: pal [1; 2; 3; 3; 2; 1].
Proof. Admitted.

Theorem pal_app_rev: forall {X:Type} (l: list X), 
  pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [|h t IH].
  - simpl. apply empty.
  - simpl. 
    assert (G: (h :: t ++ rev t ++ [h]) = (h :: (t ++ rev t) ++ [h])). {
      rewrite <- (app_assoc ).
      reflexivity.
    }
    rewrite -> G.
    apply step.
    apply IH.
Qed.

Lemma Geq: forall {X: Type} (l1 l2 l3: list X), 
  l1 = l2 -> l1 ++ l3 = l2 ++ l3.
Proof.
  intros X l1 l2 l3 H.
  rewrite -> H.
  reflexivity.
Qed.

Lemma Rev_concat: forall {X: Type} l (c: X), 
  rev (l ++ [c]) = c :: (rev l).
Proof.
  intros X l c.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. 
    apply (Geq (rev (t ++ [c])) (c :: rev t) [h]).
    apply IH.
Qed.

Lemma concat_inj: forall {X: Type} (l1 l2: list X) (x1 x2: X),
  l1 ++ [x1] = l2 ++ [x2] -> l1 = l2 /\ x1 = x2.
Proof.
  intros X l1.
  induction l1 as [| h t IH].
  - simpl.
    destruct l2 as [| l2h l2t ] eqn: El2.
    + simpl.
      intros x1 x2 H.
      split.
      * reflexivity.
      * injection H as H'.
        apply H'.
    + intros x1 x2.
      simpl.
      intros H.
      injection H as H1 H2.
      destruct l2t as [|l2th l2tt].
      * simpl in H2. discriminate H2.
      * simpl in H2. discriminate H2.
  - simpl.
    intros l2 x1 x2 H.
    destruct l2 as [| l2h l2t] eqn:El2.
    + simpl in H.
      injection H as H'1 H'2.
      destruct t as [| th tt ] eqn:Et.
      * simpl in H'2. discriminate H'2.
      * simpl in H'2. discriminate H'2.
    + simpl in H.
      injection H as H'1 H'2.
      destruct (IH l2t x1 x2 H'2) as [G1 G2].
      split.
      * rewrite <- H'1.
        rewrite <- G1.
        reflexivity.
      * apply G2.
Qed.

Theorem pal_rev: forall {X: Type} (l: list X),
  pal l -> l = rev l.
Proof.
  intros X l H.
  induction H as [| c | c l H' IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    apply (Geq (c ::l) (rev (l ++ [c])) [c]).
    rewrite -> Rev_concat.
    rewrite <- IH.
    reflexivity.
Qed.

(*
Lemma tst: forall {X: Type} l m (x: X), 
  x :: l = m ++ [x] -> ((l = nil /\ m = nil) \/ (exists l', l = l' ++ [x] /\ m = x :: l')).
Proof.
  intros X l m x H.
  generalize dependent m.
  generalize dependent x.
  destruct l as [| h t ].
  - left. split.
    + reflexivity.
    + destruct m as [| mh mt] eqn:Em.
      * reflexivity.
      * simpl in H.
        injection H as InjH.
        destruct mt as [| mtH mtT].
        -- simpl in H. discriminate H.
        -- simpl in H. discriminate H.
  - intros x m H.
    assert(G: exists k, m = x :: k). {
      destruct m as [| mh mt].
      + simpl in H. injection H as H'. discriminate H'.
      + simpl in H. injection H as H'.
        exists mt. 
        rewrite -> H'.
        reflexivity.
    }
    destruct G as [k Hm].
    right.
    exists k.
    split.
    + rewrite -> Hm in H.
      simpl in H.
      injection H as Hr.
      apply Hr.
    + apply Hm.
Qed.
*)

Lemma rev_empty: forall {X: Type} (l: list X), 
  rev l = [] -> l = [].
Proof.
  intros X l H.
  destruct l as [|h t] eqn:El.
  - reflexivity.
  - simpl in H. 
    destruct (rev t) as [| rh rt] eqn:Erev.
    + simpl in H.
      discriminate H.
    + simpl in H.
      discriminate H.
Qed.

Lemma destruct_last: forall {X: Type} (l: list X),
  l = [] \/ exists l' t, l = l' ++ [t].
Proof.
  intros X l.
  induction l as [|h t IH].
  - left. reflexivity.
  - right.
    destruct IH as [IHl | IHr].
    + exists [].
      exists h.
      rewrite -> IHl.
      reflexivity.
    + destruct IHr as [lH [tH Hh]].
      exists (h :: lH).
      exists tH.
      simpl.
      rewrite <- Hh.
      reflexivity.
Qed.

Lemma rev_add_last: forall {X: Type} l (t: X), 
  rev (l ++ [t]) = t :: (rev l).
Proof.
  intros X l.
  induction l as [| lh lt IH].
  - intros t. simpl. reflexivity.
  - intros t. simpl.
    rewrite -> IH.
    simpl.
    reflexivity.
Qed.
(*
Lemma tst3 : forall {X: Type} (h: X) l,
  h :: l = rev (h :: l) -> l = [] \/ exists l', l' = rev l' /\ h :: l' ++ [h] = h :: l.
Proof.
  intros X h l H.
  simpl in H.
  destruct (rev l) as [|revH revT] eqn:Erev.
  - apply rev_empty in Erev.
    left. apply Erev.
  - right.
    exists revT.
    split.
    + destruct (destruct_last l) as [H1 | H2].
      * rewrite -> H1 in Erev.
        simpl in Erev.
        discriminate Erev.
      * destruct H2 as [lStart [lLast lEq]].
        rewrite -> lEq in H.
        rewrite -> lEq in Erev.
        assert (G1: rev lStart = revT). {
          rewrite -> rev_add_last in Erev.
          injection Erev as Erev'1 Erev'2.
          apply Erev'2.
        }
        assert (G2: lStart = revT). {
          simpl in H.
          injection H as H'1 H'2.
          destruct (concat_inj lStart revT lLast h H'2) as [ErevT Eh].
          apply ErevT.
        }
        rewrite -> G2 in G1.
        symmetry.
        apply G1.
    + assert (G: revT ++ [h] = l -> h :: revT ++ [h] = h :: l). {
        intros Hg.
        rewrite -> Hg.
        reflexivity.
      }
      apply G.
      simpl in H.
      injection H as H'1 H'2.
      symmetry. apply H'2.
Qed.
*)
Lemma add_any_side_same_len: forall {X: Type} (l: list X) (a b: X), 
  length (a :: l) = length (l ++ [b]).
Proof.
  intros X l.
  induction l as [| h t IH].
  - intros a b. reflexivity.
  - intros a b. simpl. rewrite <- (IH a b). reflexivity.
Qed.

Lemma list_split: forall {X: Type} (l: list X),
  (exists l1   l2, length l1 = length l2 /\ l = l1 ++        l2) \/ 
  (exists l1 c l2, length l1 = length l2 /\ l = l1 ++ [c] ++ l2).
Proof.
  intros X l.
  induction l as [| h t IH].
  - left. exists []. exists [].
    simpl.
    split.
    + reflexivity.
    + reflexivity.
  - assert (G: forall l m, l = m -> h :: l = h :: m). {
      intros l m Hg.
      rewrite -> Hg. 
      reflexivity.
    }
    destruct IH as [[l1 [l2 H ]] | [l1 [c [l2 H]]]].
    + right.
      destruct (destruct_last l1) as [Hd | Hd].
      * exists []. exists h. exists [].
        simpl.
        rewrite -> Hd in H.
        simpl in H.
        destruct H as [H1 H2].
        assert (G': l2 = []). {
          destruct l2 as [| hl2 tl2].
          - reflexivity.
          - simpl in H1. discriminate H1.
        }
        rewrite -> G' in H2.
        split. reflexivity. rewrite -> H2. reflexivity.
      * destruct Hd as [l' [t' Hl1]].
        exists (h :: l').
        exists t'.
        exists l2.
        destruct H as [H1 H2].
        split.
        -- rewrite -> (add_any_side_same_len l' h t').
           rewrite <- Hl1.
           apply H1.
        -- rewrite -> H2.
           rewrite -> Hl1.
           simpl.
           apply G.
           rewrite -> app_assoc.
           simpl.
           reflexivity.
    + left.
      exists (h :: l1).
      exists (c :: l2).
      destruct H as [H1 H2].
      split.
      * simpl. rewrite -> H1. reflexivity.
      * simpl. rewrite -> H2.
        apply G.
        simpl.
        reflexivity.
Qed.

Lemma len_add_last: forall {X: Type} l (x: X), 
  length (l ++ [x]) = S (length l).
Proof.
  intros X l x.
  rewrite <- (add_any_side_same_len l x x).
  reflexivity.
Qed.


Lemma step_rev: forall {X: Type} l (x: X), 
  (x :: l ++ [x]) = rev (x :: l ++ [x]) -> l = rev l.
Proof.
  intros X l x H.
  simpl in H.
  rewrite -> rev_add_last in H.
  simpl in H.
  injection H as H1.
  destruct (concat_inj l (rev l) x x H1).
  apply H.
Qed.

Theorem pal_rev': forall {X: Type} (l : list X), 
  l = rev l -> pal l.
Proof.
  intros X l H.
  destruct (list_split l) as [Hl | Hr].
  - destruct Hl as [l1 [l2 [EqLen EqL ]]].
    generalize dependent l.
    generalize dependent l2.
    induction l1 as [| h t IH].
    + intros l2 EqLen l H EqL.
      assert (Hl2Empty: l2 = []). {
        simpl in EqLen.
        destruct l2 as [| l2h l2t].
        - reflexivity.
        - simpl in EqLen. discriminate EqLen.
      }
      rewrite -> Hl2Empty in EqL.
      simpl in EqL.
      rewrite -> EqL.
      apply empty.
    + intros l2 EqLen l H EqL.
      destruct (destruct_last l2) as [Hd | Hd].
      * rewrite -> Hd in EqLen. discriminate EqLen.
      * destruct Hd as [l' [h' El2]].
        rewrite -> El2 in EqL.
        assert (G: h = h'). {
          rewrite -> EqL in H.
          rewrite <- (app_assoc) in H.
          rewrite -> (rev_add_last ((h :: t) ++ l') h') in H.
          rewrite -> (app_assoc) in H.
          simpl in H.
          injection H as H1.
          apply H1.
        }
        rewrite <- G in EqL.
        rewrite -> EqL.
        simpl.
        rewrite <- (app_assoc).
        apply step.
        assert (G1: length t = length l'). {
          rewrite -> El2 in EqLen.
          rewrite -> len_add_last in EqLen.
          simpl.
          injection EqLen as EqLen'.
          apply EqLen'.
        }
        assert (G2: (t ++ l') = rev (t ++ l')). {
          simpl in EqL.
          rewrite -> EqL in H.
          rewrite <- (app_assoc) in H.
          destruct (step_rev (t ++ l') h H) as [H'].
          reflexivity.
        }
        apply (IH l' G1 (t ++ l') G2).
        reflexivity.
  - destruct Hr as [l1 [c [l2 [EqLen EqL ]]]].
    generalize dependent l.
    generalize dependent l2.
    induction l1 as [| h t IH].
    + intros l2 EqLen l H EqL.
      assert (Hl2Empty: l2 = []). {
        simpl in EqLen.
        destruct l2 as [| l2h l2t].
        - reflexivity.
        - simpl in EqLen. discriminate EqLen.
      }
      rewrite -> Hl2Empty in EqL.
      simpl in EqL.
      rewrite -> EqL.
      apply one.
    + intros l2 EqLen l H EqL.
      destruct (destruct_last l2) as [Hd | Hd].
      * rewrite -> Hd in EqLen. discriminate EqLen.
      * destruct Hd as [l' [h' El2]].
        rewrite -> El2 in EqL.
        assert (G: h = h'). {
          rewrite -> EqL in H.
          rewrite <- (app_assoc) in H.
          rewrite <- (app_assoc) in H.
          rewrite -> (rev_add_last (((h :: t) ++ [c]) ++ l') h') in H.
          rewrite -> (app_assoc) in H.
          simpl in H.
          injection H as H1.
          apply H1.
        }
        rewrite <- G in EqL.
        rewrite -> EqL.
        rewrite <- (app_assoc).
        rewrite <- (app_assoc).
        simpl.
        apply step.
        rewrite -> (app_assoc).
        assert (G1: length t = length l'). {
          rewrite -> El2 in EqLen.
          rewrite -> len_add_last in EqLen.
          simpl.
          injection EqLen as EqLen'.
          apply EqLen'.
        }
        assert (G2: (t ++ [c] ++ l') = rev (t ++ [c] ++ l')). {
          rewrite <- (app_assoc) in EqL.
          rewrite <- (app_assoc) in EqL.
          simpl in EqL.
          rewrite -> EqL in H.
          rewrite -> (app_assoc _ t [c] l') in H.
          destruct (step_rev (t ++ [c] ++ l') h H) as [H'].
          reflexivity.
        }
        apply (IH l' G1 (t ++ [c] ++ l') G2).
        reflexivity.
Qed.


End Pal.

Definition disjoint {X: Type} (l1 l2 : list X): Prop := 
  forall (a: X), In a l1 -> ~(In a l2).

Inductive NoDup {X: Type} : list X -> Prop :=
  | emptyNoDup : NoDup []
  | consNoDup (l: list X) (x: X) (H: NoDup l) (N: ~(In x l)) : NoDup (x :: l)
.

Search or.

Lemma not_in_sum: forall {X: Type} (x: X) (a b: list X), 
  ~ In x a /\ ~ In x b -> ~ In x (a ++ b).
Proof.
  intros X x a b [Ha Hb].
  induction a as [| h t IH].
  - simpl. apply Hb.
  - simpl.
    simpl in Ha.
    assert (G: forall A B, ~(A \/ B) -> ~A /\ ~B). {
      intros A B H.
      unfold not in H.
      split.
      + unfold not. intros HA. apply H. apply (or_introl HA).
      + unfold not. intros HB. apply H. apply (or_intror HB).
    }
    unfold not.
    intros [Hl | Hr].
    + apply (Ha (or_introl Hl)).
    + apply G in Ha.
      destruct Ha as [Hal Har].
      apply IH.
      apply Har.
      apply Hr.
Qed.



Theorem no_dup_in_concat: forall {X: Type} (l1 l2: list X), 
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 [Hnd1 [Hnd2 Hd]].
  induction l1 as [| h t IH].
  - simpl. apply Hnd2.
  - assert (G: NoDup t). {
      remember (h :: t) as k.
      destruct Hnd1 as [| l x H' N'] eqn:E.
      + discriminate Heqk.
      + injection Heqk as Heqk1 Heqk2.
        rewrite <- Heqk2.
        apply H'.
    }
    assert (G1: disjoint t l2). {
      unfold disjoint.
      unfold disjoint in Hd.
      simpl in Hd.
      intros a Inat.
      apply (Hd a (or_intror Inat)).
    }
    assert (G2': ~ In h l2). {
      unfold disjoint in Hd.
      apply Hd.
      simpl. left. reflexivity.
    }
    assert (G2'': ~ In h t). {
      remember (h :: t) as k.
      destruct Hnd1 as [| l x H' N'] eqn:E.
      - discriminate Heqk.
      - injection Heqk as Heqk1 Heqk2.
        rewrite <- Heqk2.
        rewrite <- Heqk1.
        apply N'.
    }
    assert (G2: ~ In h (t ++ l2)). {
      unfold disjoint in Hd.
      apply not_in_sum.
      split.
      + apply G2''.
      + apply G2'.
    }
    simpl.
    apply (consNoDup (t ++ l2) h (IH G G1)).
    apply G2.
Qed.









End IndProp.