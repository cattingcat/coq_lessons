From Coq Require Import Lists.List. Import ListNotations.

Definition tst (l: list nat) (H: length l > 0) : nat.
Proof.
  destruct l.
  - exfalso. inversion H.
  - apply n.
Defined. (* allows to compute *)

Print tst.

Print False_rec.

Print eq_ind.

Definition tst1 : (forall l : list nat, length l > 0 -> nat) := 
  fun (l : list nat) (H : length l > 0) =>
    match l as l' return (length l' > 0 -> nat) with
    | [] => fun (H0 : length [] > 0) =>
        False_rec nat
          (let H1 : (length [] = length [] -> False) :=
             match H0 in (_ <= n) return (n = length [] -> False) with
             | le_n _ =>
                 (fun H2 : 1 = length [] =>
                  let H3 : False :=
                    eq_ind 1 (fun e : nat => match e with
                                             | 0 => False
                                             | S _ => True
                                             end) I (length []) H2 in False_ind False H3)
             | le_S _ m H1 =>
                 fun (H2 : S m = length []) =>
                 (let H4 : False :=
                    eq_ind (S m) (fun e : nat => match e with
                                                 | 0 => False
                                                 | S _ => True
                                                 end) I (length []) H2 in False_ind (1 <= m -> False) H4) H1
             end 
            in H1 eq_refl)
    | n :: _ => fun (_ : length (n :: _) > 0) => n
    end H.

Definition lst := [1;2;3].
Lemma lst_len: length lst > 0.
Proof. simpl. auto. Qed.

Compute (tst lst lst_len).

Eval vm_compute in (tst lst lst_len).
Eval compute in (tst lst lst_len).

Eval cbv in (tst lst lst_len).
Eval lazy in (tst lst lst_len).
