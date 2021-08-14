Require Coq.extraction.Extraction.
Extraction Language OCaml.


From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import ImpCEvalFun.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

Import ImpCEvalFun.

(* creates file in current dir (where coqide opened) *)
Extraction "./imp1.ml" ceval_step.