From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "+".
Print sumor. (* decision type, 
                  left - result of type X, 
                  right - proof that result doesn't exist *)
Print sumbool.
Print sum.