(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__085, cataloged as "Divisibility by 3 Rule": a
  finite base-10 natural-number sum is divisible by 3 exactly when the sum
  of its coefficients is divisible by 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val divisibility_by_3_rule =
  ``!d : num -> num.
      !n : num.
        divides 3
          (SIGMA
             (\i : num. 10 EXP i * d i)
             (count (SUC n))) <=>
        divides 3
          (SIGMA
             (\i : num. d i)
             (count (SUC n)))``;
