(*
  Statement-only formalization of VERINA artifact verina_advanced_14,
  cataloged as "ifPowerOfFour": the recursive Boolean program determines
  whether a natural number is an exact power of four.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val ifPowerOfFour_precond_def = new_definition (
  "ifPowerOfFour_precond_def",
  ``ifPowerOfFour_precond (n : num) <=> T``
);

val ifPowerOfFour_helper_def = Define `
  (ifPowerOfFour_helper 0 = F) /\
  (ifPowerOfFour_helper (SUC 0) = T) /\
  (ifPowerOfFour_helper (SUC (SUC l)) =
     if (l + 2) MOD 4 = 0 then
       ifPowerOfFour_helper ((l + 2) DIV 4)
     else
       F)
`;

val ifPowerOfFour_def = new_definition (
  "ifPowerOfFour_def",
  ``ifPowerOfFour (n : num) = ifPowerOfFour_helper n``
);

val ifPowerOfFour_postcond_def = new_definition (
  "ifPowerOfFour_postcond_def",
  ``ifPowerOfFour_postcond (n : num) (result : bool) <=>
      (result <=> ?m : num. n = 4 EXP m)``
);

val ifPowerOfFour_spec_satisfied =
  ``!n : num.
      ifPowerOfFour_precond n ==>
      ifPowerOfFour_postcond n (ifPowerOfFour n)``;
