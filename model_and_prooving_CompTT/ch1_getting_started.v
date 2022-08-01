
(* Ex 1.2.1 *)
Fixpoint min (a: nat) (b: nat) : nat := 
  match a, b with
  | S a', S b' => S (min a' b')
  | _, _ => O
  end.

Compute (min 7 5).
Search true.

Fixpoint is_eq (a: nat) (b: nat) : bool := 
  match a, b with
  | O, O => true
  | S a', S b' => is_eq a' b'
  | _, _ => false
  end.