(*
  Statement-only formalization of "The Solution of a Cubic" from Hundred Theorems item 037. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val solution_of_a_cubic =
  ``!a b c d p q r s t omega x : complex.
      a <> 0 /\
      p = (3 * a * c - b pow 2) / (9 * a pow 2) /\
      q =
        (9 * a * b * c - 2 * b pow 3 - 27 * a pow 2 * d) /
        (54 * a pow 3) /\
      omega pow 3 = 1 /\
      omega <> 1 /\
      (if p = 0 then
         s pow 3 = 2 * q
       else
         r pow 2 = q pow 2 + p pow 3 /\
         s pow 3 = q + r /\
         t * s = p)
      ==>
      (if p = 0 then
         (a * x pow 3 + b * x pow 2 + c * x + d = 0 <=>
          x = s - b / (3 * a) \/
          x = s * omega - b / (3 * a) \/
          x = s * omega pow 2 - b / (3 * a))
       else
         s <> 0 /\
         (a * x pow 3 + b * x pow 2 + c * x + d = 0 <=>
          x = s - t - b / (3 * a) \/
          x = s * omega - t * omega pow 2 - b / (3 * a) \/
          x = s * omega pow 2 - t * omega - b / (3 * a)))``;
