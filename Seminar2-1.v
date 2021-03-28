

Section Equality.

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
:= 
  fun xey => 
    match xey with
    | eq_refl => eq_refl: eq (f x) (f x)
    end.

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:=
  fun '(eq_refl) => fun '(eq_refl) => 
    (eq_refl : eq (f x) (f x)).

(** extra exercise *)
Definition tst_id_eq (A : Type) (p : A) : ((fun (x : A) => x) p) = p
:= 
  eq_refl.

(*
Definition congId A {x y : A} (p : x = y) : f_congr (fun x => x) p = p
:=
  eq_refl.
*)

About fst.

(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= 
  fun abab => conj (@f_congr (A * B) A fst (a1, b1) (a2, b2) abab) (@f_congr (A * B) B snd (a1, b1) (a2, b2) abab).

End Equality.
