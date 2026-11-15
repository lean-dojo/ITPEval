(*
  Statement-only formalization of VERINA corpus artifact verina_basic_25,
  catalog title "sumAndAverage": the executable natural-number program sums
  the range from zero through n and computes its IEEE-754 binary64 average,
  under the positive precision bound and its exact postcondition. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;
open binary_ieeeTheory machine_ieeeTheory;

val sumAndAverage_precond_def = new_definition (
  "sumAndAverage_precond_def",
  ``sumAndAverage_precond (n : num) <=>
      n > 0 /\ n < 2 EXP 53``
);

val sumAndAverage_range_def = new_definition (
  "sumAndAverage_range_def",
  ``sumAndAverage_range (n : num) =
      GENLIST (\i : num. i) (n + 1)``
);

val sumAndAverage_rangeSum_def = new_definition (
  "sumAndAverage_rangeSum_def",
  ``sumAndAverage_rangeSum (n : num) =
      SUM (sumAndAverage_range n)``
);

val sumAndAverage_natToFloat_def = new_definition (
  "sumAndAverage_natToFloat_def",
  ``sumAndAverage_natToFloat (n : num) =
      int_to_fp64 roundTiesToEven (&n)``
);

val sumAndAverage_def = new_definition (
  "sumAndAverage_def",
  ``sumAndAverage (n : num) =
      if n <= 0 then
        ((0 : int), fp64_posZero)
      else
        let sum = sumAndAverage_rangeSum n in
        let average =
          fp64_div
            roundTiesToEven
            (sumAndAverage_natToFloat sum)
            (sumAndAverage_natToFloat n)
        in
          ((&sum : int), average)``
);

val sumAndAverage_postcond_def = new_definition (
  "sumAndAverage_postcond_def",
  ``sumAndAverage_postcond
      (n : num) (result : int # word64) <=>
      (n = 0 ==>
        FST result = 0 /\
        fp64_equal (SND result) fp64_posZero) /\
      (n > 0 ==>
        FST result = &(n * (n + 1) DIV 2) /\
        fp64_equal
          (SND result)
          (fp64_div
            roundTiesToEven
            (sumAndAverage_natToFloat (n * (n + 1) DIV 2))
            (sumAndAverage_natToFloat n)))``
);

val sumAndAverage_spec_satisfied =
  ``!n : num.
      sumAndAverage_precond n ==>
      sumAndAverage_postcond n (sumAndAverage n)``;
