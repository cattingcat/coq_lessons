 
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
Proof. Admitted.

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


Inductive prop_holds (A : Prop) : Type :=
  | a_holds : A -> prop_holds A.



Definition frob_to_lem :
  (forall (A : Type) (P : A -> Prop) (Q : Prop), (forall x, Q \/ P x) <-> (Q \/ forall x, P x))
  ->
  (forall (Q : Prop), Q \/ ~ Q)
:=
  fun frob (tQ : Prop) =>
    match frob (prop_holds tQ) (fun _ => False) tQ with
    | conj fw _ => 
      match fw (fun ph => match ph with a_holds _ q => or_introl q end) with
      | or_introl q => or_introl q
      | or_intror xPx => or_intror (fun Q => xPx (a_holds tQ Q))
      end
    end.


Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
:= conj lem_to_frob frob_to_lem.


End Quantifiers.


Variable PP : Prop.
Variable frob: Frobenius2.
Check frob PP (fun _ => False) PP.







(* Section ExtensionalEqualityAndComposition. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:= 
  erefl.


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


Search "=1".
Print frefl.
Print erefl.
Print eq_trans.

Search Logic.eq_refl.
Print Logic.eq_refl.


(*

            Parameter             Index
                |                   |
  Inductive eq (A : Type) (x : A) : A -> Prop :=  
    eq_refl : eq x x
                 | |
             param ind

  match someEq in (_ = gx)
                   |
                impossible to match 
      parameter, but possible to match index

  Index changable durint unification

*)


(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f => frefl f.

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:= fun f g efg x => match (efg x) in (_ = gx) return (gx = f x) with
                    | erefl => erefl
                    end.


Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h.
Proof. intros. intro x. rewrite (H x). apply (H0 x). Qed.

Print eqext_trans.

(** Exercise: Transitivity *)
Definition eqext_trans2 :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:= fun f g h efg egh x =>
    (* Imagine that after PM all "right = side" replaced with "left = side" *)
    (* after unification "hx" will be replaced with "g x" *)
    match (egh x) in (_ = hx) return (f x = hx) with
    | erefl => (efg x)
    end.


Definition succ_inj (n m: nat) : n.+1 = m.+1 -> n = m :=
                        (* sm - will be replaced with (S n) during unification *)
                                              (* Also (S n).-1 willbe calculated *)
  fun Sn_Sm => match Sn_Sm in (_ = sm) return (n = sm.-1) with
               | erefl => erefl
               end.

Definition or_introl_inj (A B: Prop) (p1 p2: A) :
  or_introl p1 = or_introl p2 :> (A \/ B) -> p1 = p2
:=
  fun eq =>
    match eq 
      in (_ = oil2)
      return (p1 = if oil2 is or_introl p2' then p2' else p2)
    with
    | erefl => erefl p1
    end.



(* return clause will be calculated twice. 1 - before PM, 2 - after PM *)
Definition discr_bool: false = true -> False 
:=
  fun (eq: false = true) =>
    match eq
      in (_      = tr)
      return   (if tr then False else True)   (* large elimination, not possible for Prop *)
                (*  ^  tr will be true BEFORE pattern mach *)
    with
    | erefl => I (* after matching, return clause will be True*)
    end.

Definition discr_bool_r: true = false -> False 
:=
  fun (eq: true = false) =>
    match eq
      in (_      = tr)
      return   (if tr then True else False)
    with
    | erefl => I
    end.

Locate "<>".


Fail Definition neq_sym A (x y: A) :
  x <> y -> y <> x
:=
  fun (neq_xy: x <> y) (eq_yx: y = x) =>
    match eq_yx 
      in (_ = a)
      return False
    with
    | erefl => neq_xy _
    end.


Definition unification_test: 
  (cons 1 (cons 2 (cons 3 nil))) = app (cons 1 (cons 2 nil)) (cons 3 nil)
:= erefl.

Definition neq_sym A (x y: A) :
  x <> y -> y <> x
:=
  fun (neq_xy: x <> y) (eq_yx: y = x) =>
    (match eq_yx 
      in (_ = a)
      return (a <> y -> False) (* before pattern match a := x, afler a := y *)
    with
    | erefl => fun (neq_xy': y <> y) => neq_xy' (erefl y) (* "a" become "y = y" after patterm matching *)
    end) neq_xy.


Definition congr (A B: Type) (f: A -> B) x y: 
  x = y -> f x = f y
:=
  fun eq_xy =>
    match eq_xy
      in (_ = a)
      return (f x = f a)
    with
    | erefl => erefl (f x)
    end.

Definition addn0 : forall n, n + 0 = n
:=
  fix rec (n: nat) : n + 0 = n :=
    match n as a return (a + 0 = a) with (* a  will be replaced with constructors  0 and (S n') *)
    | 0 => erefl      (* 0 + 0 = 0 *)
                 (* (S n') + 0 = S n' *) 
    | S n' => congr nat nat S (n' + 0) n' (rec n')
    end.


Definition Pred (n: nat) : Type :=
  if n is S n' then nat else unit.

Definition predn_dep (n: nat): Pred n :=
  if n is S n' then n' else tt.

Compute Pred 0.
Compute predn_dep 0.

Compute Pred 42.
Compute predn_dep 42.

Definition pred (n: {x: nat | ~~ (x == 0)}) : nat :=
  match n with 
  | exist x pneq0 => predn x
  end.

Definition pred2 (n: {x: nat | x <> 0}) : nat :=
  match n with 
  | exist x pneq0 => predn x
  end.


Definition pred3 (n: {x: nat | x <> 0}) : nat :=
  match n with 
  | exist x pneq0 =>(match x 
                      as a 
                      return ((a = 0 -> False) -> nat)
                     with
                     | 0    => fun contra => match (contra erefl) with end
                     | S x' => fun _ => x'
                     end) pneq0
  end.


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