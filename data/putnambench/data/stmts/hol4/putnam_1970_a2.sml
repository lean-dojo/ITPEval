(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a2:
  a real quadratic form with negative discriminant, perturbed by cubic terms,
  has no nonzero zeros sufficiently near the origin. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1970_a2 =
  ``!A B C D E F G : real.
      B pow 2 - 4 * A * C < 0
      ==>
      ?delta : real.
        delta > 0 /\
        ~(?x y : real.
            0 < x pow 2 + y pow 2 /\
            x pow 2 + y pow 2 < delta pow 2 /\
            A * x pow 2 + B * x * y + C * y pow 2 +
            D * x pow 3 + E * x pow 2 * y + F * x * y pow 2 +
            G * y pow 3 = 0)``;
