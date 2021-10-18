From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition bool_Prop_equiv P b := 
  b = true <-> P.


Lemma test_bool_Prop_equiv b P: bool_Prop_equiv P b -> P \/ ~P.
Proof.
  case: b; case => hlr hrl.
    by left; apply hlr.
  right. move=> hP. by move: (hrl hP).
Qed.