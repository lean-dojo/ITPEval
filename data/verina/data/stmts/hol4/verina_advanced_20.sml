(*
  Statement-only formalization of VERINA artifact verina_advanced_20,
  cataloged as "isItEight": the executable Boolean program tests whether an
  integer is divisible by eight or has the digit eight in its absolute value.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory;

val hasDigitEightFuel_def = Define `
  (hasDigitEightFuel 0 (m : num) = F) /\
  (hasDigitEightFuel (SUC fuel) m =
     if m <= 0 then
       F
     else if m MOD 10 = 8 then
       T
     else
       hasDigitEightFuel fuel (m DIV 10))
`;

val hasDigitEight_def = new_definition (
  "hasDigitEight_def",
  ``hasDigitEight (m : num) = hasDigitEightFuel m m``
);

val isItEight_precond_def = new_definition (
  "isItEight_precond_def",
  ``isItEight_precond (n : int) <=> T``
);

val isItEight_def = new_definition (
  "isItEight_def",
  ``isItEight (n : int) =
      let absN = Num (ABS n)
      in
        (n % 8 = 0 \/ hasDigitEight absN)``
);

val isItEight_postcond_def = new_definition (
  "isItEight_postcond_def",
  ``isItEight_postcond (n : int) (result : bool) <=>
      let absN = Num (ABS n)
      in
        ((n % 8 = 0 \/
          ?i : num. (absN DIV (10 EXP i)) MOD 10 = 8) <=>
         result)``
);

val isItEight_spec_satisfied =
  ``!n : int.
      isItEight_precond n ==>
      isItEight_postcond n (isItEight n)``;
