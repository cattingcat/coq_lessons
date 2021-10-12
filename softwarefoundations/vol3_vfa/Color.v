Require Import List.
Require Import Setoid. (* Generalized rewriting *)
Require Import FSets. (* Efficient functional sets *)
Require Import FMaps. (* Efficient functional maps *)
Require Import PArith. (* Positives *)
From VFA Require Import Perm.

Module E := PositiveOrderedTypeBits.
Print Module E.
Print E.t.

Module S <: FSetInterface.S := PositiveSet.
Print Module PositiveSet.
Print Module S.
Print S.elt.


Module M <: FMapInterface.S := PositiveMap.
Print Module M.
Print M.E.

Module WF := WFacts_fun E M. (* Library of useful lemmas about maps *)
Module WP := WProperties_fun E M. (* More useful stuff about maps *)
Print Module WF.
Print Module WP.
Check E.lt.

Lemma lt_strict: StrictOrder E.lt.
Proof. exact M.ME.MO.IsTO.lt_strorder. Qed.

Lemma lt_proper: Proper (eq ==> eq ==> iff) E.lt.
Proof. exact M.ME.MO.IsTO.lt_compat. Qed.

(* TODO *)