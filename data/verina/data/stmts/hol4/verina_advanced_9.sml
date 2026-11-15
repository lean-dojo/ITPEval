(*
  Statement-only formalization of VERINA artifact verina_advanced_9,
  cataloged as "countSumDivisibleBy": the executable program counts the
  natural numbers below n whose decimal digit sum is divisible by positive d,
  under its precondition and postcondition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val sumOfDigits_go_def = Define `
  (sumOfDigits_go
      0 (n : num) (acc : num) =
     acc) /\
  (sumOfDigits_go
      (SUC fuel) n acc =
     if n = 0 then
       acc
     else
       sumOfDigits_go fuel (n DIV 10) (acc + n MOD 10))
`;

val sumOfDigits_def = new_definition (
  "sumOfDigits_def",
  ``sumOfDigits (x : num) =
      sumOfDigits_go x x 0``
);

val countSumDivisibleBy_precond_def = new_definition (
  "countSumDivisibleBy_precond_def",
  ``countSumDivisibleBy_precond (n : num) (d : num) <=>
      d > 0``
);

val isSumDivisibleBy_def = new_definition (
  "isSumDivisibleBy_def",
  ``isSumDivisibleBy (x : num) (d : num) <=>
      sumOfDigits x MOD d = 0``
);

val countSumDivisibleBy_go_def = Define `
  (countSumDivisibleBy_go
      0 (acc : num) (d : num) =
     acc) /\
  (countSumDivisibleBy_go
      (SUC i) acc d =
     let acc' =
       if isSumDivisibleBy i d then acc + 1 else acc
     in
       countSumDivisibleBy_go i acc' d)
`;

val countSumDivisibleBy_def = new_definition (
  "countSumDivisibleBy_def",
  ``countSumDivisibleBy (n : num) (d : num) =
      countSumDivisibleBy_go n 0 d``
);

val countSumDivisibleBy_postcond_def = new_definition (
  "countSumDivisibleBy_postcond_def",
  ``countSumDivisibleBy_postcond
      (n : num) (d : num) (result : num) <=>
      LENGTH
        (FILTER
          (\x : num. x < n /\ sumOfDigits x MOD d = 0)
          (COUNT_LIST n)) -
        result = 0 /\
      result <=
        LENGTH
          (FILTER
            (\x : num. x < n /\ sumOfDigits x MOD d = 0)
            (COUNT_LIST n))``
);

val countSumDivisibleBy_spec_satisfied =
  ``!(n : num) (d : num).
      countSumDivisibleBy_precond n d ==>
      countSumDivisibleBy_postcond
        n d (countSumDivisibleBy n d)``;
