From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive exp: Type :=
  | con (n: nat)
  | add (a: exp) (b: exp)
  | sub (a: exp) (b: exp).

Fixpoint eval (e: exp): nat :=
  match e with
  | con n => n
  | add a b => eval a + eval b
  | sub a b => eval a - eval b
  end.


Inductive comm: Type :=
  | addc
  | subc
  | push (n: nat).

Print list.

Fixpoint r (pr: list comm) (s: list nat): list nat :=
  match pr, s with 
  | (cons addc pr'), (cons a (cons b  rest)) => r pr' (cons (a + b) rest)
  | (cons subc pr'), (cons a (cons b  rest)) => r pr' (cons (a - b) rest)
  | (cons (push n) pr'), stack => r pr' (cons n stack)
  | [::], s => s
  | _, _ => nil
  end.

Fixpoint compile (e: exp): list comm :=
    match e with 
    | con n => cons (push n) nil
    | add a b => compile b ++ compile a ++  (cons addc nil) 
    | sub a b => compile b ++ compile a ++ (cons subc nil)
    end.

(* 20.3.1 *)
Lemma stepc: forall e rest stack, 
  r (compile e ++ rest) stack = r rest (cons (eval e) stack).
Proof.
  elim => [n //| a IH b IH' | a IH b IH'] rest stack.
  - rewrite /compile -/compile /eval -/eval.
    rewrite -catA IH'.
    rewrite -catA IH.
    rewrite cat1s.
    by rewrite /r -/r.
  - rewrite /compile -/compile /eval -/eval.
    rewrite -catA IH'.
    rewrite -catA IH.
    rewrite cat1s.
    by rewrite /r -/r.
Qed.

(* 20.3.2 *)
Theorem correctc: forall e, r (compile e) [::] = [:: (eval e)].
Proof.
  elim => [ n //= | a IH b IH' | a IH b IH' ].
  - by rewrite /compile -/compile 2!stepc /r /eval -/eval.
  - by rewrite /compile -/compile 2!stepc /r /eval -/eval.
Qed.

(* 20.4 *)
Fixpoint d (pr: list comm) (exps: list exp): list exp :=
  match pr, exps with 
  | [::], e => e
  | [:: addc & rest], [:: e1, e2 & exps] => d rest [:: add e1 e2 & exps]
  | [:: subc & rest], [:: e1, e2 & exps] => d rest [:: sub e1 e2 & exps]
  | [:: push n & rest], exps => d rest [:: con n & exps]
  | _, _ => [::]
  end.

(* 20.4.1 *)
Lemma stepd: forall e pr b, d (compile e ++ pr) b = d pr [:: e & b ].
Proof.
  elim => [ n pr b // | e1 IH e2 IH' pr b | e1 IH e2 IH' pr b ].
  - rewrite /compile -/compile -catA IH' -catA IH cat1s.
    by rewrite /d -/d.
  - rewrite /compile -/compile -catA IH' -catA IH cat1s.
    by rewrite /d -/d.
Qed.

(* 20.4.2 *)
Theorem correctd: forall e, d (compile e) [::] = [:: e ].
Proof.
  elim => [ n // | a IH b IH' | a IH b IH' ];
    by rewrite /compile -/compile stepd stepd /d -/d.
Qed.
  