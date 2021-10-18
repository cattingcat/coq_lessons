From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.


(** * Arithmetic expression language *)


(** NOTE: If you don't need this homework graded for you university,
          please, do _not_ submit it through the CS club website. *)

(** NOTE: In a later homework we are going to prove some properties of the
functions this homework asks you to implement. Please keep your code so you can
reuse it later. *)


(** Define is a simple language of arithmetic expressions consisting of
constants (natural numbers) and arbitrarily nested additions, subtractions and
multiplications *)
Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr
| Mult of expr & expr.

(** Let us define a special notation for our language.
    We reuse the standard arithmetic notations here, but only inside
    double square brackets (see examples below) *)

(* This means we declare `expr` as an identifier referring to a 'notation
entry' *)
Declare Custom Entry expr.
(* And we let the parser know `expr` is associated with double brackets, so
inside double brackets the parser will use notations associated with custom
`expr` entries *)
Notation "'[[' e ']]'" := e (e custom expr at level 0).

(* Numerals can be used without wrapping those in the `Const` constructor *)
Notation "x" :=
  (Const x)
    (in custom expr at level 0, x bigint).

Notation "( x )" := x (in custom expr, x at level 2).
Notation "x + y" := (Plus x y) (in custom expr at level 2, left associativity).

(* Define notations for subtraction and multiplication.
   Hint: lower level means higher priority.
   Your notations should start with `in custom expr` as above. *)
Notation "x - y" := (Minus x y) (in custom expr at level 2, left associativity).
Notation "x * y" := (Mult x y) (in custom expr at level 1, left associativity).

(** Here is how we write Plus (Const 0) (Plus (Const 1) (Const 2)) *)
Check [[
          0 + (1 + 2)
      ]].
(** And this is Plus (Plus (Const 0) (Const 1)) (Const 2) *)
Check [[
          (0 + 1) + 2
      ]].

(* Make sure the following are parsed as expected.
   What query can you use to do that? *)

Set Printing All.
Check [[
          ((0 + 1) + 2) + 3
      ]].
Check [[
          0 + (1 + (2 + 3))
      ]].
Check [[
          0 * 1 + 2
      ]].
Check [[
          0 + 1 * 2
      ]].
Unset Printing All.


(** Write an evaluator for the expression language which fixes its semantics.
Basically, the semantics of the expression language should be the same as
the corresponding Coq functions `addn`, `subn`, `muln`. *)
Fixpoint eval (e : expr) : nat :=
  match e with 
  | Const c => c
  | Plus a b => eval a + eval b
  | Minus a b => eval a - eval b
  | Mult a b => eval a * eval b
  end.


(** Some unit tests *)
(** We haven't discussed in depth what `erefl` means yet.
    But for now, let's just assume if the following lines
    typecheck then the equalities below hold *)
Check erefl : eval [[ 0 - 4 ]] = 0.
Check erefl : eval [[ 0 + (2 - 1) ]] = 1.
Check erefl : eval [[ (0 + 1) + 2 ]] = 3.
Check erefl : eval [[ 2 + 2 * 2 ]] = 6.
Check erefl : eval [[ (2 + 2) * 2 ]] = 8.



(** * Compiling arithmetic expressions to a stack language *)

(** Here is a "low-level" stack language which can serve as the target language
for a compiler from the arithmetic expression language above.
See, for instance, this page for more detail:
https://en.wikipedia.org/wiki/Stack-oriented_programming.
A program in this language is a list of instructions, each of which manipulates
a stack of natural numbers. There are instructions for pushing constants onto
the stack and for adding/subtracting/muliplying the top two elements of the
stack, popping them off the stack, and pushing the result onto the stack. *)

Inductive instr := Push (n : nat) | Add | Sub | Mul.


(*
Feel free to define your own notations for the stack operations
to make it easier writing unit tests
For example, this is one possible way to start:
Notation " << n >> " := (Push n) (at level 0, n constr).
*)


(* Feel free to either define your own datatype to represent lists or reuse the
`seq` datatype provided by Mathcomp (this is why this file imports the `seq`
module at the beginning). Btw, `seq` is just a notation for the standard `list`
datatype.
    Inductive list (A : Type) : Type :=
      | nil
      | cons of A & list A.
You can construct new lists (sequences) like so:
  - [::]           --  notation for the `nil` constructor;
  - x :: xs        --  notation for the `cons` constructor;
  - [:: 1; 2; 3]   --  notation for a sequence of three elements 1, 2 and 3.
Using `seq`, we can define the type of programs as follows:

And the type of stacks like so:

*)

Definition prog := seq instr.
Definition stack := seq nat.

Declare Custom Entry prog.
Notation "'[|' e '|]'" := e (e custom prog at level 0).
Notation "x" :=
  ([:: Push x ])
    (in custom prog at level 0, x bigint).

Notation "x y +" :=
  (x ++ y ++ [:: Add ])
    (in custom prog at level 1).
Notation "x y -" :=
  (x ++ y ++ [:: Sub ])
    (in custom prog at level 1).

Notation "x y *" :=
  (x ++ y ++ [:: Mul ])
    (in custom prog at level 1).

Set Printing All.
Check [| 2 2 + 3 + 4 * |].
Unset Printing All.


(** The [run] function is an interpreter for the stack language. It takes a
 program (list of instructions) and the current stack, and processes the program
 instruction-by-instruction, returning the final stack. *)
Fixpoint run (p : prog) (s : stack) : stack :=
  match p with 
  | Push n :: ps => run ps (n :: s)
  | Add :: ps => 
    match s with 
    | a :: b :: ss => run ps (a + b :: ss)
    | _ => [::]
    end
  | Sub :: ps =>
    match s with 
    | a :: b :: ss => run ps (a - b :: ss)
    | _ => [::]
    end
  | Mul :: ps =>
    match s with 
    | a :: b :: ss => run ps (a * b :: ss)
    | _ => [::]
    end
  | _ => s
  end.


Compute run [:: (Push 1); (Push 2); Add ] [::].


(** Unit tests: *)
Check erefl :
  run [:: (Push 1); (Push 2); Add ] [::] = [:: 3 ].





(** Now, implement a compiler from "high-level" expressions to "low-level" stack
programs and do some unit tests. *)
Fixpoint compile (e : expr) : prog :=
  match e with 
  | Plus  l r => compile r ++ compile l ++ [:: Add ]
  | Minus l r => compile r ++ compile l ++ [:: Sub ]
  | Mult  l r => compile r ++ compile l ++ [:: Mul ]
  | Const n => [:: Push n ]
  end.


Compute (run (compile [[ 2 + 3 ]])).
Compute (run (compile [[ 2 + 3 * 4 ]])).


(** Do some unit tests *)
Check erefl :
  compile [[ 2 + 3 ]] = [:: Push 3; Push 2; Add ].

Check erefl :
  compile [[ 2 + 3 * 2 ]] = [:: Push 2; Push 3; Mul; Push 2; Add ].

(* Some ideas for unit tests:
  - check that `run (compile e) [::] = [:: eval e]`, where `e` is an arbitrary expression;
  - check that `compile` is an injective function
*)


(** Optional exercise: decompiler *)

(** Implement a decompiler turning a stack program into the corresponding
expression *)
(* Hint: you might want to introduce a recursive helper function `decompile'` to
 reuse it for `decompile`. *)

Definition stack_expr := seq expr.

Fixpoint decompile_helper (p : prog) (s : stack_expr) : stack_expr :=
  match p with 
  | Push n :: ps => decompile_helper ps (Const n :: s)
  | Add :: ps => 
    match s with
    | a :: b :: ss => decompile_helper ps (Plus a b :: ss)
    | _ => s
    end
  | Sub :: ps =>
    match s with
    | a :: b :: ss => decompile_helper ps (Minus a b :: ss)
    | _ => s
    end
  | Mul :: ps =>
    match s with
    | a :: b :: ss => decompile_helper ps (Mult a b :: ss)
    | _ => s
    end
  | _ => s
  end.

About option.

Definition decompile (p : prog) : option expr :=
  match decompile_helper p [::] with
  | [:: e] => Some e
  | _ => None
  end.

Compute (decompile [:: Push 2; Push 3; Add ]).
Compute (decompile [| 2 3 4 * + |]).


(** Unit tests *)
Check erefl :
  decompile [:: Push 2; Push 3; Add ] = some [[ 3 + 2 ]].

Check erefl :
  decompile [| 2 3 4 * + |] = some [[ 4 * 3 + 2 ]].

Check erefl :
  decompile (compile [[ 2 + 3 ]]) = some [[ 2 + 3 ]].

Check erefl :
  decompile (compile [[ 2 + 3 * 4 ]]) = some [[ 2 + 3 * 4 ]].

(* Some ideas for unit tests:
  - check that `decompile (compile e) = Some e`, where `e` is an arbitrary expression
*)