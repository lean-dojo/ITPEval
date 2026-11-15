(*
  Statement-only formalization of VERINA artifact verina_advanced_23,
  cataloged as "isPowerOfTwo": the fuel-bounded executable Boolean program
  repeatedly divides a positive integer by two and recognizes exactly the
  positive integer powers of two. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory;

val isPowerOfTwo_precond_def = new_definition (
  "isPowerOfTwo_precond_def",
  ``isPowerOfTwo_precond (n : int) <=> T``
);

val isPowerOfTwo_aux_def = Define `
  (isPowerOfTwo_aux 0 (m : int) = F) /\
  (isPowerOfTwo_aux (SUC fuel) m =
     if m = 1 then
       T
     else if m % 2 <> 0 then
       F
     else
       isPowerOfTwo_aux fuel (m / 2))
`;

val isPowerOfTwo_def = new_definition (
  "isPowerOfTwo_def",
  ``isPowerOfTwo (n : int) =
      if n <= 0 then
        F
      else
        isPowerOfTwo_aux (Num (ABS n)) n``
);

val isPowerOfTwo_pow_def = Define `
  (isPowerOfTwo_pow (base : int) 0 = 1) /\
  (isPowerOfTwo_pow base (SUC exp) =
     base * isPowerOfTwo_pow base exp)
`;

val isPowerOfTwo_postcond_def = new_definition (
  "isPowerOfTwo_postcond_def",
  ``isPowerOfTwo_postcond (n : int) (result : bool) <=>
      if result then
        ?x : num. isPowerOfTwo_pow 2 x = n /\ n > 0
      else
        ~(?x : num. isPowerOfTwo_pow 2 x = n /\ n > 0)``
);

val isPowerOfTwo_spec_satisfied =
  ``!n : int.
      isPowerOfTwo_precond n ==>
      isPowerOfTwo_postcond n (isPowerOfTwo n)``;
