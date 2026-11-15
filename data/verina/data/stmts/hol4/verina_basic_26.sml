(*
  Statement-only formalization of VERINA corpus artifact verina_basic_26,
  catalog title "isEven": the executable integer parity test returns true
  exactly when the input has zero remainder modulo two and satisfies its
  two-direction correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val isEven_precond_def = new_definition (
  "isEven_precond_def",
  ``isEven_precond (n : int) <=> T``
);

val isEven_def = new_definition (
  "isEven_def",
  ``isEven (n : int) = (n % 2 = 0)``
);

val isEven_postcond_def = new_definition (
  "isEven_postcond_def",
  ``isEven_postcond (n : int) (result : bool) <=>
      (result ==> n % 2 = 0) /\
      (~result ==> n % 2 <> 0)``
);

val isEven_spec_satisfied =
  ``!n : int.
      isEven_precond n ==>
      isEven_postcond n (isEven n)``;
