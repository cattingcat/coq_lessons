Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Module ProofObjects.
Import IndProp.

Print IndProp.ev.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print ev_4.

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).


Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_4.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 ev_4).



Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS _ (ev_SS _ H).


Definition add1 : nat -> nat.
  intros n.
  Show Proof.
  apply S.
  Show Proof.
  apply n. Defined.

Print add1.



Module Props.

  Module And.
    Inductive and (P Q : Prop) : Prop :=
      | conj : P -> Q -> and P Q.
    Arguments conj [P] [Q].
    Notation "P /\ Q" := (and P Q) : type_scope.
  
    Print prod.

    Theorem proj1' : forall P Q,
      P /\ Q -> P.
    Proof.
      intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
      Show Proof.
    Qed.

    Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
    Proof.
      intros P Q. split.
      - intros [HP HQ]. split.
        + apply HQ.
        + apply HP.
      - intros [HQ HP]. split.
        + apply HP.
        + apply HQ.
    Qed.

    Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
      fun p => fun q => fun r => fun pq => fun qr => 
        match pq with 
        | conj p' q' => 
          match qr with
          | conj q'' r' => conj p' r'
          end
        end.
  End And.

  Module Or.
    Inductive or (P Q : Prop) : Prop :=
      | or_introl : P -> or P Q
      | or_intror : Q -> or P Q.
    Arguments or_introl [P] [Q].
    Arguments or_intror [P] [Q].
    Notation "P \/ Q" := (or P Q) : type_scope.

    Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
      fun P Q HP => or_introl HP.

    Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
    Proof.
      intros P Q HP. left. apply HP.
    Qed.

    Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
      fun P Q R HPQ HPR HQR =>
        match HPQ with
        | or_introl HP => HPR HP
        | or_intror HQ => HQR HQ
        end.

    Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
    Proof.
      intros P Q R HPQ HPR HQR.
      destruct HPQ as [HP | HQ].
      - apply HPR. apply HP.
      - apply HQR. apply HQ.
    Qed.

    Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
      fun P Q PQ => 
        match PQ with
        | or_introl HP => or_intror HP
        | or_intror HQ => or_introl HQ
        end.
  End Or.

  Module Ex.
    Inductive ex {A : Type} (P : A -> Prop) : Prop :=
      | ex_intro : forall (x : A), P x -> ex P.

    Print ex_intro.

    Notation "'exists' x , p" :=
      (ex (fun x => p))
        (at level 200, right associativity) : type_scope.

    Check ex (fun n => ev n) : Prop.

    Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
      ex_intro _ 1 (ev_SS _ ev_0).
  End Ex.


  Module TrueFalse.
    Inductive True : Prop :=
      | I : True.

    Definition p_implies_true : forall P, P -> True :=
      fun P HP => I.

    Inductive False : Prop := .

    Definition ex_falso_quodlibet' : forall P, False -> P :=
      fun P F => match F with end.
  End TrueFalse.
End Props.

Module MyEquality.
  Inductive eq {X:Type} : X -> X -> Prop :=
    | eq_refl : forall x, eq x x.
  Notation "x == y" := (eq x y)
                         (at level 70, no associativity)
                       : type_scope.

  Lemma four: 2 + 2 == 1 + 3.
  Proof.
    apply eq_refl.
  Qed.
  
  Definition four' : 2 + 2 == 1 + 3 :=
    eq_refl 4.

  Definition singleton : forall (X:Type) (x:X), [] ++ [x] == x :: []  :=
    fun (X:Type) (x:X) => eq_refl [x].


  Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
    x == y -> forall (P: X -> Prop), P x -> P y.
  Proof.
    intros.
    destruct H.
    apply H0.
  Qed.

  Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
    (forall (P : X -> Prop), P x -> P y) -> x == y.
  Proof.
    intros.
    destruct (H (fun i => i == x)).
    - apply eq_refl.
    - apply eq_refl.
  Qed.
End MyEquality.

End ProofObjects.
