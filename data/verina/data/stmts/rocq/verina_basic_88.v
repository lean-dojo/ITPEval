(* Statement-only formalization of VERINA corpus artifact verina_basic_88,
   catalog title "ToArray": executable conversion of an arbitrary integer
   list to an array with the same length and elements in the same order,
   together with its unconditional precondition, postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Lists.List ZArith.

Module VerinaBasic88.

Definition ToArray_precond (_xs : list Z) : Prop :=
  True.

Definition ToArray
    (xs : list Z)
    (_h_precond : ToArray_precond xs) : list Z :=
  xs.

Definition ToArray_postcond
    (xs result : list Z)
    (_h_precond : ToArray_precond xs) : Prop :=
  length result = length xs /\
  forall i : nat,
    (i < length xs)%nat ->
    nth i result 0%Z = nth i xs 0%Z.

Theorem ToArray_spec_satisfied
    (xs : list Z)
    (h_precond : ToArray_precond xs) :
  ToArray_postcond
    xs (ToArray xs h_precond) h_precond.
Admitted.

End VerinaBasic88.
