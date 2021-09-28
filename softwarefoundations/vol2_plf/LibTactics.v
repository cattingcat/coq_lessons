Set Implicit Arguments.
Require Import Coq.Lists.List.
Declare Scope ltac_scope.

(* Very important to remove hint trans_eq_bool from LibBool,
   otherwise eauto slows down dramatically:
  Lemma test : forall b, b = false.
  time eauto 7. (* takes over 4 seconds to fail! *) *)
Local Remove Hints Bool.trans_eq_bool : core.