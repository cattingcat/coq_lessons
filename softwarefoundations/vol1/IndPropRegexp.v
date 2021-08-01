(*From LF Require Export Logic.*)
From Coq Require Import Lia.
Require Import Coq.Strings.Ascii.
Require Import List.

Module IndPropRegexp.

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

Search nil.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : nil =~ EmptyStr
  | MChar x : cons x nil =~ (Char x)
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
  | MStar0 re : nil =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).


Search list.
Definition string := list ascii.


Module HelperLemmas.
  Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
  Proof.
    intros.
    split.
    - intros. constructor.
    - intros _. apply H.
  Qed.

  Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
  Proof.
    intros.
    split.
    - apply H.
    - intros. destruct H0.
  Qed.

  Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
  Proof.
    intros.
    apply not_equiv_false.
    unfold not. intros. inversion H.
  Qed.

  Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = nil.
  Proof.
    split.
    - intros. inversion H. reflexivity.
    - intros. rewrite H. apply MEmpty.
  Qed.

  Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
  Proof.
    intros.
    apply not_equiv_false.
    unfold not. intros. inversion H.
  Qed.

  Lemma char_nomatch_char :
    forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
  Proof.
    intros.
    apply not_equiv_false.
    unfold not.
    intros.
    apply H.
    inversion H0.
    reflexivity.
  Qed.

  Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = nil.
  Proof.
    split.
    - intros. inversion H. reflexivity.
    - intros. rewrite H. apply MChar.
  Qed.

  Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
  Proof.
    intros.
    split.
    - intros. inversion H. exists s1, s2. split.
      + reflexivity.
      + split. apply H3. apply H4.
    - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
      rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
  Qed.

  Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    (nil =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
  Proof.
    intros. split.
    - intros Hmat.
      (* MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2) *)
      inversion Hmat.
      destruct s1 as [| s1h s1t].
      + left.
        split. apply H1.
        simpl. apply H3.
      + right.
        simpl in H0.
        injection H0 as H0h H0.
        exists s1t, s2.
        split.
        * symmetry. apply H0.
        * split.
          ** rewrite -> H0h in H1. apply H1.
          ** apply H3.
    - intros [ [ Hnil Hasre1] | [ s0 [ s1 [ Es [ Has0re0 Hs1re1 ] ] ] ] ].
      + (*MApp s1 re1 s2 re2 (H1 : s1 =~ re1) (H2 : s2 =~ re2): (s1 ++ s2) *)
        apply (MApp nil re0 (a :: s) re1 Hnil Hasre1).
      + assert(G: a :: s = (a :: s0) ++ s1). {
          rewrite -> Es. simpl. reflexivity.
        }
        rewrite -> G.
        apply (MApp (a :: s0) re0 s1 re1 Has0re0 Hs1re1).
  Qed.

  Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> (s =~ re0 \/ s =~ re1).
  Proof.
    intros. split.
    - intros. inversion H.
      + left. apply H2.
      + right. apply H1.
    - intros [ H | H ].
      + apply MUnionL. apply H.
      + apply MUnionR. apply H.
  Qed.

  Lemma star_empty_empty: forall (s: string), 
    s =~ Star EmptyStr -> s = nil.
  Proof.
    intros.
    remember (Star EmptyStr) as k eqn:Ek.
    induction H as [| c 
                    | s1 re1 s2 re2 H1 IH1 H2 IH2
                    | s1 re1 re2 H1 IH
                    | re1 s2 re2 H2 IH
                    | re
                    | s1 s2 re H1 IH1 H2 IH2 ].
    - (* MEmpty  *) discriminate Ek.
    - (* MChar *) discriminate Ek.
    - (* MApp *) discriminate Ek.
    - (* MUnionL *) discriminate Ek.
    - (* MUnionR *) discriminate Ek.
    - (* MStar0 *) reflexivity.
    - (* MStarApp *) injection Ek as Ek'.
      rewrite -> Ek' in H2.
      rewrite -> Ek' in H1.
      assert(G: s1 = nil). {
        apply empty_matches_eps.
        apply H1.
      }
      rewrite -> G. simpl. 
      apply IH2.
      rewrite -> Ek'.
      reflexivity.
  Qed.

  Search (?l ++ nil = ?l).
  Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
  Proof.
    intros.
    split.
    + intros H.
      remember (Star re) as k eqn:Ek.
      remember (a :: s) as acs eqn:Eacs.
      induction H as [| c 
                      | s1 re1 s2 re2 H1 IH1 H2 IH2
                      | s1 re1 re2 H1 IH
                      | re1 s2 re2 H2 IH
                      | re'
                      | s1 s2 re' H1 IH1 H2 IH2 ].
      - (* MEmpty  *) discriminate Ek.
      - (* MChar *) discriminate Ek.
      - (* MApp *) discriminate Ek.
      - (* MUnionL *) discriminate Ek.
      - (* MUnionR *) discriminate Ek.
      - (* MStar0 *) discriminate Eacs.
      - (* MStarApp *) 
        destruct s1 as [| s1h s1t] eqn:Es1.
        * simpl in Eacs.
          apply (IH2 Ek Eacs).
        * simpl in Eacs.
          injection Eacs as Eacs'h Eacs't.
          exists s1t, s2.
          split.
          ** symmetry. apply Eacs't.
          ** split.
             *** rewrite -> Eacs'h in H1. injection Ek as Ek. rewrite -> Ek in H1. apply H1.
             *** apply H2.
    + intros [ s0 [ s1 [ Es [Has0 Hs1 ] ] ] ].
      rewrite -> Es.
      assert (G: a :: s0 ++ s1 = (a :: s0) ++ s1). { reflexivity. }
      rewrite -> G.
      (* MStarApp s1 s2 re (H1 : s1 =~ re) (H2 : s2 =~ (Star re))   : (s1 ++ s2) =~ (Star re) *)
      apply (MStarApp (a :: s0) s1 _ Has0 Hs1).
  Qed.


  Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

End HelperLemmas.


Import HelperLemmas.

Definition refl_matches_eps m := forall re : reg_exp ascii, reflect (nil =~ re) (m re).

Fixpoint match_eps (re: reg_exp ascii) : bool :=
  match re with 
  | EmptyStr => true
  | EmptySet => false
  | Char _ => false
  | App r1 r2 => match_eps r1 && match_eps r2
  | Union r1 r2 => match_eps r1 || match_eps r2
  | Star _ => true
  end.

  Search (?l1 ++ ?l2 = nil).

Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros re.
  induction re as [ | | c | r1 IHl r2 IHr | r1 IHl r2 IHr | r IH].
  - simpl. apply ReflectF. unfold not. intros H. inversion H.
  - simpl. apply ReflectT. apply MEmpty.
  - simpl. apply ReflectF. unfold not. intros H. inversion H.
  - simpl. 
    destruct (match_eps r1).
    + destruct (match_eps r2).
      ++ simpl. inversion IHl as [IHl' | _]. inversion IHr as [IHr' | _]. apply ReflectT. 
         apply (MApp nil r1 nil r2 IHl' IHr').
      ++ simpl. apply ReflectF. unfold not. intros H. inversion H. inversion IHr.
         apply H5.
         assert (G: s2 = nil). { destruct (app_eq_nil s1 s2 H1). apply H7. }
         rewrite -> G in H4. apply H4.
    + simpl. apply ReflectF. unfold not. intros H. inversion H. inversion IHl.
      apply H5.
      assert (G: s1 = nil). { destruct (app_eq_nil s1 s2 H1). apply H6. }
      rewrite -> G in H3. apply H3.
  - simpl. 
    destruct (match_eps r1).
    + simpl. apply ReflectT. 
      assert (G: nil =~ r1). {inversion IHl. apply H. }
      apply (MUnionL nil r1 r2 G).
    + destruct (match_eps r2).
      ++ simpl. apply ReflectT. 
         assert (G: nil =~ r2). {inversion IHr. apply H. }
         apply (MUnionR r1 nil r2 G).
      ++ simpl. apply ReflectF. unfold not. intros H. inversion IHl.
         apply H0. inversion H. apply H3. 
         inversion IHr. exfalso. apply H5. apply H3.
  - simpl. apply ReflectT. apply MStar0.
Qed.

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char t => if eqb t a then EmptyStr else EmptySet
  | App r1 r2 =>  (* TODO *)
    if match_eps r1 
    then 
      match derive a r1 with
      | EmptySet => derive a r2
      | o => App o r2
      end
    else App (derive a r1) r2
  | Union r1 r2 => 
    match derive a r1 with
    | EmptySet => derive a r2
    | o => o
    end
  | Star r =>  
    let d := derive a r in
    if match_eps d then Star r else App d (Star r)
  end.

Module DeriveTests.
  Example c := ascii_of_nat 99.
  Example d := ascii_of_nat 100.

  (* "c" =~ EmptySet: *)
  Example test_der0 : match_eps (derive c (EmptySet)) = false.
  Proof. simpl. reflexivity. Qed.

  (* "c" =~ Char c:  *)
  Example test_der1 : match_eps (derive c (Char c)) = true.
  Proof. simpl. reflexivity. Qed.

  (* "c" =~ Char d: *)
  Example test_der2 : match_eps (derive c (Char d)) = false.
  Proof. simpl. reflexivity. Qed.

  (* "c" =~ App (Char c) EmptyStr: *)
  Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
  Proof. simpl. reflexivity. Qed.

  (* "c" =~ App EmptyStr (Char c): *)
  Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
  Proof. simpl. reflexivity. Qed.

  (* "c" =~ App (Star d) (Char c): *)
  Example test_der41 : match_eps (derive c (App (Star (Char d)) (Char c))) = true.
  Proof. simpl. reflexivity. Qed.

  (* "dc" =~ App (Star d) (Char c): *)
  Example test_der42 : match_eps (derive c (derive d (App (Star (Char d)) (Char c)))) = true.
  Proof. simpl. reflexivity. Qed.

  (* "c" =~ Star c: *)
  Example test_der5 : match_eps (derive c (Star (Char c))) = true.
  Proof. simpl. reflexivity. Qed.

  (* "cd" =~ App (Char c) (Char d): *)
  Example test_der6 :
    match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
  Proof. simpl. reflexivity. Qed.

  (* "cd" =~ App (Char d) (Char c): *)
  Example test_der7 :
    match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
  Proof. simpl. reflexivity. Qed.

End DeriveTests.

Search (?s = nil ++ ?s).

Lemma derive_corr : derives derive.
Proof.
  unfold derives, is_der.
  intros a re.
  generalize dependent a.
  induction re as [ | | c | r1 IHl r2 IHr | r1 IHl r2 IHr | r IH].
  - simpl. intros. split.
    + intros H. inversion H.
    + intros H. inversion H.
  - simpl. intros. split.
    + intros H. inversion H.
    + intros H. inversion H.
  - simpl. intros. split.
    + intros H. inversion H. 
      destruct (eqb_spec c c).
      * apply MEmpty.
      * exfalso. apply n. reflexivity.
    + intros H.
      destruct (eqb_spec c a) as [Eca | Eca].
      * rewrite <- Eca. 
        inversion H.
        apply (MChar c).
      * inversion H.
  - simpl. intros. split.
Admitted.


Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool. Admitted.

Theorem regex_refl : matches_regex regex_match.
Proof. Admitted.

Module End.