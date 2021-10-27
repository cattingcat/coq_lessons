From mathcomp
  Require Import ssreflect ssrbool ssrnat.

Print bool.

Print nat.

Fixpoint my_plus n m := 
 match n with
 | 0     => m
 | n'.+1 => let: tmp := my_plus n' m in tmp.+1
 end.


Definition sum_no_zero n := 
 let: P := (fun n => if n is 0 then unit else nat) in
 nat_rec P tt (fun n' (m: P n') => 
                 match n' return P n' -> _ with
                 | 0 => fun _ => 1
                 | n1.+1 => fun m => my_plus m (n'.+1) 
                 end m) n.

About nat_rec.

Check sum_no_zero 0.
Check sum_no_zero 1.

Search "filt" (_ -> list _).

Search _ ((?X -> ?Y ) -> _ ?X -> _ ?Y ).
Search _ (?a * ?b : nat).
Search _ (?a * ?b : Type).

Locate "_ + _".

Inductive my_prod (A B : Type) : Type := my_pair of A & B.

Fail Check my_pair tt 1.

Arguments my_pair [A B].
Notation "X ** Y" := (my_prod X Y ) (at level 2).
Notation "( X ,, Y )" := (my_pair X Y ).

Check my_pair tt 1.


Theorem false_absutd: False -> (1 = 2).
Proof.
case.
Restart.
apply: False_ind.
Qed.
