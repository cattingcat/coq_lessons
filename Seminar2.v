 
Section PropositionalLogic.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
:=
  fun '(conj a _) => a.


Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
:=
  fun ab => fun bc => fun a => bc (ab a).


Definition HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C
:=
  fun abc => fun ab => fun a => abc a (ab a).


(* ~ A = A -> False *)
(* ~ ~ A = (A -> False) -> False *)
(* ~ ~ ~ A = ((A -> False) -> False) -> False *)
Definition DNE_triple_neg :
  ~ ~ ~ A -> ~ A
:=
  fun nnna => fun a => nnna (fun a2f => a2f a).


Definition or_comm :
  A \/ B -> B \/ A
:=
  fun ab =>
    match ab with 
    | or_introl l => or_intror l
    | or_intror r => or_introl r
    end.

End PropositionalLogic.



Section Quantifiers.

Definition forall_conj_to (A: Type) (P Q : A -> Prop) :
  (forall x, P x /\ Q x) -> (forall x, Q x /\ P x)
:=
  fun x_pq => fun x => 
    match x_pq x with 
    | conj p q => conj q p
    end.

Definition forall_disj_to (A: Type) (P Q : A -> Prop) :
  (forall x, P x \/ Q x) -> (forall x, Q x \/ P x)
:=
  fun x_pq => fun x => 
    match x_pq x with 
    | or_introl p => or_intror p
    | or_intror q => or_introl q
    end.


Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.
Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
:= 
  conj (forall_conj_to T P Q) (forall_conj_to T Q P).
  

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
:=
  conj (forall_disj_to T P Q) (forall_disj_to T Q P).

(* (ex_intro x px -> False) -> x -> P x -> False*)
Definition not_exists_forall_not :
  ~(exists x, P x) -> forall x, ~P x
:=
  fun (x_px2F : (@ex T P) -> False) => fun (x : T) => fun (px : P x) => 
    x_px2F (@ex_intro T P x px).


Definition exists_forall_not_ :
(exists x, A -> P x) -> (forall x, ~P x) -> ~A.

(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).


Definition lem_to_frob1  : 
  (forall {Q : Prop}, Q \/ ~ Q) -> (forall (A : Type) (P : A -> Prop) (Q : Prop), (forall x, Q \/ P x) -> (Q \/ forall x, P x))
:=
  fun lem _ _ qt => fun x2QOrPx => 
    match lem qt with 
    | or_introl q => or_introl q
    | or_intror notQ => or_intror (fun x => match x2QOrPx x with
      | or_intror px => px
      | or_introl q => match notQ q with end
      end)
    end.

Definition lem_to_frob2 : 
  (forall (Q : Prop), Q \/ ~ Q) -> (forall (A : Type) (P : A -> Prop) (Q : Prop), (Q \/ forall x, P x) -> (forall x, Q \/ P x))
:=
  fun lem _ _ qt => fun qOrPx => 
    match lem qt with 
    | or_introl q => (fun x => or_introl q)
    | or_intror notQ => 
      match qOrPx with
      | or_introl q => match notQ q with end
      | or_intror xPx => (fun x => or_intror (xPx x))
      end
    end.

Definition lem_to_frob : 
  (forall (Q : Prop), Q \/ ~ Q) -> (forall (A : Type) (P : A -> Prop) (Q : Prop), (forall x, Q \/ P x) <-> (Q \/ forall x, P x))
:=
  fun lem a p q => conj (@lem_to_frob1 lem a p q) (@lem_to_frob2 lem a p q).

Definition lem_to_Frobenius2 : LEM -> Frobenius2
:= lem_to_frob.


(*
Definition frob_to_lem  (A : Type) (P : A -> Prop) (Q : Prop) : 
  ((forall x, Q \/ P x) <-> (Q \/ forall x, P x)) -> (Q \/ ~ Q)
:=
  (* (forall x, Q \/ P x) -> (Q \/ forall x, P x) *)
  (* (Q \/ forall x, P x) -> (forall x, Q \/ P x) *)
  fun '(conj fw bw) => 
    match fw 
      (fun x => or_introl True) 
    with
    | or_introl q => or_introl q
    | or_intror x2Px => or_introl q
    end.
*)



(*
Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
:=
*)

End Quantifiers.








(* Section ExtensionalEqualityAndComposition. *)

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:=


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:=

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:=

(** Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:=

(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:=

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:=

End ExtensionalEqualityAndComposition.


From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:=

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:=