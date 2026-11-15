(*
  Statement-only formalization of VERINA corpus artifact verina_basic_78,
  catalog title "MultipleReturns": the executable integer-pair program returns
  the sum and difference of two integers and satisfies its precondition and
  postcondition correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val MultipleReturns_precond_def = new_definition (
  "MultipleReturns_precond_def",
  ``MultipleReturns_precond (x : int) (y : int) <=> T``
);

val MultipleReturns_def = new_definition (
  "MultipleReturns_def",
  ``MultipleReturns (x : int) (y : int) =
      let more = x + y in
        let less = x - y in
          (more, less)``
);

val MultipleReturns_postcond_def = new_definition (
  "MultipleReturns_postcond_def",
  ``MultipleReturns_postcond
      (x : int) (y : int) (result : int # int) <=>
      FST result = x + y /\
      SND result + y = x``
);

val MultipleReturns_spec_satisfied =
  ``!(x : int) (y : int).
      MultipleReturns_precond x y ==>
      MultipleReturns_postcond x y (MultipleReturns x y)``;
