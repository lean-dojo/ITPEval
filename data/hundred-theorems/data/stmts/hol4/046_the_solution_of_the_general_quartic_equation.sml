(*
  Statement-only formalization of "The Solution of the General Quartic Equation" from Hundred
  Theorems item 046. Ferrari's formulas characterize all roots of a complex quartic in the
  biquadratic and cubic-resolvent cases. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val solution_of_the_general_quartic_equation =
  ``!a b c d e p q r s t u v w x : complex.
      a <> 0 /\
      p = (8 * a * c - 3 * b pow 2) / (8 * a pow 2) /\
      q =
        (b pow 3 - 4 * a * b * c + 8 * a pow 2 * d) /
        (8 * a pow 3) /\
      r =
        (16 * a * b pow 2 * c + 256 * a pow 3 * e -
         3 * b pow 4 - 64 * a pow 2 * b * d) /
        (256 * a pow 4) /\
      (if q = 0 then
         t pow 2 = p pow 2 - 4 * r /\
         v pow 2 = (0 - p + t) / 2 /\
         w pow 2 = (0 - p - t) / 2
       else
         u pow 3 - p * u pow 2 - 4 * r * u +
           4 * p * r - q pow 2 = 0 /\
         s pow 2 = u - p /\
         v pow 2 = 4 * s pow 2 - 8 * (u - q / s) /\
         w pow 2 = 4 * s pow 2 - 8 * (u + q / s))
      ==>
      (if q = 0 then
         (a * x pow 4 + b * x pow 3 + c * x pow 2 + d * x + e = 0 <=>
          x = v - b / (4 * a) \/
          x = 0 - v - b / (4 * a) \/
          x = w - b / (4 * a) \/
          x = 0 - w - b / (4 * a))
       else
         (a * x pow 4 + b * x pow 3 + c * x pow 2 + d * x + e = 0 <=>
          x = (0 - 2 * s - v) / 4 - b / (4 * a) \/
          x = (0 - 2 * s + v) / 4 - b / (4 * a) \/
          x = (2 * s - w) / 4 - b / (4 * a) \/
          x = (2 * s + w) / 4 - b / (4 * a)))``;
