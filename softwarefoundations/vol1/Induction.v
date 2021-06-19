Module Induction.


Theorem add_0_r_firsttry : forall (n : nat),
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Print add_0_r_firsttry.

Theorem minus_n_n : forall (n : nat),
  n - n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.


Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' H].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    reflexivity.
  - simpl.
    intros m.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_Sm_Sn : forall n m : nat,
  (S n) + m = n + (S m).
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    reflexivity.
  - simpl.
    intros m.
    rewrite <- H.
    simpl.
    reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    intros m.
    simpl.
    rewrite -> add_0_r_firsttry.
    reflexivity.
  - simpl.
    intros m.
    rewrite <- plus_n_Sm.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.


Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n.
  induction n as [| n' H].
  - simpl.
    reflexivity.
  - simpl.
    intros m p.
    rewrite -> H.
    reflexivity.
Qed.




Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> H.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Fixpoint even (n : nat) : bool :=
  match n with 
  | O => true
  | S O => false
  | S (S m) => even m
  end.

Lemma double_neg : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    reflexivity.
  - rewrite -> H.
    simpl.
    rewrite -> double_neg.
    reflexivity.
Qed.


Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). {
    reflexivity.
  }
  rewrite -> H.
  reflexivity. 
Qed.


Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : n + m = m + n). {
    rewrite add_comm. 
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Print plus_rearrange_firsttry.


Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H1 : n + (m + p) = (n + m) + p). {
    rewrite -> add_assoc.
    reflexivity.
  }
  assert (H2 : m + (n + p) = (m + n) + p). {
    rewrite -> add_assoc.
    reflexivity.
  }
  rewrite -> H1.
  rewrite -> H2.
  assert (H3 : n + m = m + n). {
    rewrite -> add_comm.
    reflexivity.
  }
  rewrite -> H3.
  reflexivity.
Qed.


Lemma second_mult_expand : forall m n : nat,
  n * (S m) = n + n * m.
Proof.
  induction n as [| n' H].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> H.
    rewrite -> add_shuffle3.
    reflexivity.
Qed.


Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [| m' H].
  - simpl.
    assert (G : n * 0 = 0). {
      induction n as [| n' G'].
      - simpl.
        reflexivity.
      - simpl.
        rewrite -> G'.
        reflexivity.
    }
    rewrite -> G.
    
    reflexivity.
  - simpl.
    rewrite -> H.
    rewrite -> second_mult_expand.
    reflexivity.
Qed.






Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => eqb i j
  | _, _ => false
  end.
Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S i, S j => leb i j
  | O, S _ => true
  | _, _ => false
  end.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Check leb.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros n.
  induction n as [| n' H ].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.


Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n.
  destruct n as [| n'].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros n.
  destruct n as [|].
  - reflexivity.
  - reflexivity.
Qed.


Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| p' I].
  - simpl.
    rewrite -> H.
    reflexivity.
  - simpl.
    rewrite -> I.
    reflexivity.
Qed. 

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> add_comm.
  simpl.
  reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b as [|].
  assert (H: forall i : bool, orb i (negb i) = true). {
    intros i.
    destruct i.
    - reflexivity.
    - reflexivity.
  }
  - simpl.
    rewrite -> H.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [| p' H ].
  - simpl.
    rewrite -> mul_0_r.
    rewrite -> mul_0_r.
    rewrite -> mul_0_r.
    reflexivity.
  - rewrite -> second_mult_expand.
    rewrite -> second_mult_expand.
    rewrite -> second_mult_expand.
    rewrite -> H.
    assert (G: forall a b c d : nat, (a + b) + (c + d) = (a + c) + (b + d)). {
      intros a b c d.
      rewrite <- add_assoc.
      assert (G' : b + (c + d) = c + d + b). {
        rewrite -> add_comm.
        reflexivity.
      }
      rewrite -> G'.
      assert (G'' : c + d + b = c + (d + b)). {
        rewrite -> add_assoc.
        reflexivity.
      }
      rewrite -> G''.
      rewrite -> add_assoc.
      assert (G''' : d + b = b + d). {
        rewrite -> add_comm.
        reflexivity.
      }
      rewrite -> G'''.
      reflexivity.
    }
    rewrite -> G.
    reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> mult_plus_distr_r.
    rewrite -> H.
    reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' H ].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  replace (n + m) with (m + n).
  rewrite <- add_assoc.
  reflexivity.

  rewrite -> add_comm.
  reflexivity.
Qed.


Module BinNat.
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (b : bin) : bin :=
  match b with
  | Z => B1 Z
  | B0 i => B1 i
  | B1 i => B0 (incr i)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 i => 2 * (bin_to_nat i)
  | B1 i => 1 + 2 * (bin_to_nat i)
  end.

Theorem bin_to_nat_pres_incr : forall (b: bin),
  bin_to_nat(incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [| b' H | b' H ].
  - simpl.
    reflexivity.
  - simpl. 
    reflexivity.
  - simpl.
    rewrite -> add_0_r_firsttry.
    rewrite -> add_0_r_firsttry.
    rewrite -> H.
    assert (G: forall a b : nat, S (a + b) = a + (S b)). {
      intros a b.
      induction a as [| a' G' ].
      - simpl.
        reflexivity.
      - simpl.
        rewrite -> G'.
        reflexivity.
    }
    rewrite -> G.
    simpl.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin := 
  match n with
  | O => B0 Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [| n' H ].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> H.
    reflexivity.
Qed.

Theorem bin_nat_bin : forall b : bin, nat_to_bin (bin_to_nat b) = b.
Proof.
  (* Impossible *)
Admitted.



Fixpoint repeatB0 (n: nat) (zb: bin) : bin :=
  match n with
  | O => zb
  | S n' => B0 (repeatB0 n' zb)
  end.


Fixpoint normalize' (zerosAmount: nat) (b : bin) : bin := 
  match b with
  | Z => Z
  | B0 i => normalize' (S zerosAmount) i
  | B1 i => repeatB0 zerosAmount (B1 (normalize' O i))
  end.

Definition normalize (b : bin) : bin := 
  match b with
  | Z => B0 Z
  | b' => normalize' O b'
  end.

(*
Lemma normalize_preserves_incr: forall (b: bin), 
  normalize (incr b) = incr (normalize b).
Proof.
  intros b.
  induction b as [| b' H | b' H ].
  - unfold normalize.
    simpl.
    reflexivity.
  - simpl.
    
    

Lemma double_n_is_one_more_zero_to_bin: forall (n : nat), 
  nat_to_bin (n + n) = normalize (B0 (nat_to_bin n)).
Proof.
  intros n.
  induction n as [| n' H ].
  - unfold normalize.
    simpl.
    reflexivity.
  - simpl.
    rewrite -> add_comm.
    simpl.
    rewrite -> H.





Theorem bin_nat_bin_is_normalize: forall (b : bin), 
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b as [| b' H | b' H ].
  - unfold normalize.
    simpl.
    reflexivity.
  - unfold normalize.
    simpl.
    rewrite -> add_0_r_firsttry.
    destruct b' as [| b'0 | b'1 ].
    * simpl.
      reflexivity.
    * 

*)






End BinNat.


End Induction.
