(*
  Statement-only formalization of VERINA corpus artifact verina_basic_59,
  catalog title "DoubleQuadruple": the total executable integer program
  returns a pair whose first component is twice the input and whose second
  component is twice the first. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val DoubleQuadruple_precond_def = new_definition (
  "DoubleQuadruple_precond_def",
  ``DoubleQuadruple_precond (x : int) <=> T``
);

val DoubleQuadruple_def = new_definition (
  "DoubleQuadruple_def",
  ``DoubleQuadruple (x : int) =
      let a = (2 : int) * x in
      let b = (2 : int) * a in
        (a, b)``
);

val DoubleQuadruple_postcond_def = new_definition (
  "DoubleQuadruple_postcond_def",
  ``DoubleQuadruple_postcond
      (x : int) (result : int # int) <=>
      FST result = (2 : int) * x /\
      SND result = (2 : int) * FST result``
);

val DoubleQuadruple_spec_satisfied =
  ``!x : int.
      DoubleQuadruple_precond x ==>
      DoubleQuadruple_postcond
        x (DoubleQuadruple x)``;
