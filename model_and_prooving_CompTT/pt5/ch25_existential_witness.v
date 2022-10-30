From Coq Require Import Lia.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decidable p := (forall x, dec (p x)).
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Implicit Types n k: nat.

Section WO.
  Variable p: nat -> Prop.
  Variable p_dec: decidable p.

  Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Definition pad3 n (d: T n) : T n :=
    C n (fun h => C (S n) (fun h1 => C (S (S n)) (fun h2 =>
       let (phi) := d in
       let (phi1) := phi h in
       let (phi2) := phi1 h1 in
       phi2 h2))).

  Lemma T_base n :
    p n -> T n.
  Proof.
    intros H. constructor. intros H1. destruct (H1 H).
  Qed.

  Lemma T_step n :
    T (S n) -> T n.
  Proof.
    intros H. constructor. intros _. exact H.
  Qed.

  Lemma T_zero n :
    T n -> T 0.
  Proof.
    induction n as [|n IH].
    - auto.
    - intros H. apply IH. apply T_step, H.
  Qed.

  Lemma V n :
    p n -> T 0.
  Proof.
    intros H. eapply T_zero, T_base, H.
  Qed.
  
  Lemma W' :
    forall n, T n -> sig p.
  Proof.
    refine (fix F n a {struct a} := let (phi) := a in
                         match p_dec n with
                           inl H => _ | inr H => _
                         end).
    - exact (Sig p n H).
    - exact (F (S n) (phi H)).
  Qed.
  
  Theorem W :
    ex p -> sig p.
  Proof.
    intros H. apply (W' 0).
    destruct H as [n H].
    apply (V n), H.
  Qed.
 
  Definition elim_T
    : forall q: nat -> Type, (forall n, (~p n -> q (S n)) -> q n) -> forall n, T n -> q n
    := fun q f => fix F n a := let (phi) := a in f n (fun h => F (S n) (phi h)).

  Goal forall q g n phi,
      elim_T q g n (C n phi) = g n (fun h => elim_T q g (S n) (phi h)).
  Proof.
    reflexivity.
  Qed.

  (** W' can be defined with the eliminator for T *)
  
  Goal forall n, T n -> sig p.
  Proof.
    refine (elim_T _ (fun n IH => _)). cbn in IH.
    destruct (p_dec n) as [H|H].
    - exists n. exact H.
    - exact (IH H).
  Qed.


  (** W' can also be defined  with eliminator Coq derives for T *)
  
  Goal forall n, T n -> sig p.
  Proof.
    induction 1 as [n phi IH].
    destruct (p_dec n) as [H|H].
    - exists n. exact H.
    - exact (IH H).
  Qed.

  (** Existential characterisation of T *)

  Fact T_step_add k n :
    T (k + n) -> T n.
  Proof.
    induction k as [|k IH].
    - auto. 
    - intros H. apply IH, T_step, H.
  Qed.

  Fact T_p_zero n :
    p n -> T 0.
  Proof.
    intros H%T_base%T_zero. exact H.
  Qed.

  Fact T_ex_ge n :
    T n <-> exists k, k >= n /\ p k.
  Proof.
    split.
    - revert n.
      refine (elim_T _ (fun n IH => _)). cbn in IH.
      destruct (p_dec n) as [H|H].
      + exists n. auto.
      + destruct (IH H) as (k&H1&H2).
        exists k. split. lia. exact H2.
    - intros (k&H1&H2). apply (T_step_add (k - n)).
      replace (k - n + n) with k by lia.
      apply T_base, H2.
  Qed.
      
End WO.

Section PlayWithT.
  Goal T (fun x => x > 3) 4.
  Proof. constructor. intros contra. exfalso. auto. Qed.

  Goal T (fun x => x > 3) 1.
  Proof. 
    constructor. intros _. 
    constructor. intros _.
    constructor. intros _.
    constructor. intros contra. exfalso. auto.
  Qed.

  Goal T (fun x => x < 3) 4.
  Proof. constructor. Admitted.
End PlayWithT.


(* 25.1.2 *)
Section MyA.
  Inductive A: Prop := Ca (f: True -> A).

  Lemma n_a: ~A.
  Proof.
    refine (fix F a := let (f) := a in _).
    apply F, f, I.
  Qed.
End MyA.

(* 24.3.5 *)
Section InfPath.
  Variable p: nat -> nat -> Prop.
  Variable p_dec: forall x y, dec (p x y).
  Variable p_total: forall x, exists y, p x y.

  Definition fa (x: nat): Sigma y, p x y.
  Proof.
    Print ex.
    refine (let (y, t) := W _ _ (p_total x) in _).
    - apply p_dec.
    - exists y.
      apply t.
  Defined.

  Fixpoint fb (x: nat) (n: nat) {struct n}: nat :=
    match n with
    | 0 => x
    | S n' => let (y, _) := fa (fb x n') in y
    end.

  Lemma fb_correct: forall x n, p (fb x n) (fb x (S n)).
  Proof.
  intros x n.
  induction n.
  - unfold fb.
    destruct (fa x).
    auto.
  - unfold fb. fold fb.
    destruct (fa (fb x n)).
    destruct (fa x0).
    auto.
  Qed.
End InfPath.

(* 24.3.6 *)
Section Qwe_24_3_6.
  Variable f: nat -> bool.

  Goal (exists x, f x = true) -> {x & f x = true}.
  Proof.
    apply W.
    intro x.
    destruct (f x).
    - constructor.
      auto.
    - right.
      intro contr. discriminate.
  Qed.

  Goal {x & f x = true} -> (exists x, f x = true).
  Proof.
    intros [x h].
    exists x.
    auto.
  Qed.
End Qwe_24_3_6.


(* 24.3.7 *)
(* 24.3.8 *)

(* 24.4.1 *)
(* 24.4.2 *)
(* 24.4.3 *)





(** Binary witness operator *)

Section W2.
  (** We assume a paiting bijection *)
  Variable P: nat -> nat -> nat.
  Variable pi1 pi2: nat -> nat.
  Variable pi1_eq: forall x y, pi1 (P x y) = x.
  Variable pi2_eq: forall x y, pi2 (P x y) = y.
  
  Variable p: nat -> nat -> Prop.
  Variable p_dec: forall x y, dec (p x y).

  Theorem W2:
    (exists x y, p x y) -> Sigma x y, p x y.
  Proof.
    intros H.
    pose (q n := p (pi1 n) (pi2 n)).
    destruct (W q) as [n H1].
    - intros n.
      destruct (p_dec (pi1 n) (pi2 n)) as [H1|H1].
      + left. apply H1.
      + right. apply H1.
    - destruct H as (x&y&H). exists (P x y). hnf.
      rewrite pi1_eq, pi2_eq. exact H.
    - exists (pi1 n), (pi2 n). exact H1.
  Qed.
End W2.

(** Disjunctive witness operator *)

Section W_or.
  Variable p: nat -> Prop.
  Variable p_dec: decidable p.
  Variable q: nat -> Prop.
  Variable q_dec: decidable q.

  Theorem W_or:
    ex p \/ ex q -> sig p + sig q.
  Proof.
    intros H0.
    destruct (W (fun n => p n \/ q n)) as [n H].
    - intros n.
      destruct (p_dec n) as [H|H].
      2: destruct (q_dec n) as [H1|H1].
      + left. left. exact H.
      + left. right. exact H1.
      + right. intros [H2|H2]; auto.
    - destruct H0 as  [[n H0]|[n H0]]; eauto.
    - destruct (p_dec n) as [H1|H1].
      2: destruct (q_dec n) as [H2|H2].
      + eauto.
      + eauto.
      + exfalso. destruct H; auto.
  Qed.
End W_or.

Section Step_indexed_eqdec.
  Variable X: Type.
  Variable f: X -> X -> nat -> bool.
  Variable f_prop: forall x y, x = y <-> exists n, f x y n = true.
  Goal eqdec X.
  Proof.
    intros x y.
    enough (Sigma n, f x x n = true) as [n H].
    { destruct (f x y n) eqn:H1.
      - left. apply f_prop. exists n. exact H1.
      - right. intros <-. congruence. }
    apply W.
    - intros n.
      destruct (f x x n).
      + left. auto.
      + right. intros [=].
    - apply f_prop. reflexivity.
  Qed.
End Step_indexed_eqdec.