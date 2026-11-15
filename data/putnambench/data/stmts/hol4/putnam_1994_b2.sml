(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b2:
  a real parameter admits a straight line intersecting the corresponding
  quartic in exactly four distinct real points if and only if it is less than
  243/8. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val putnam_1994_b2 =
  ``!c : real.
      ((?m b : real.
          let intersections =
            {x : real |
               m * x + b =
                 x pow 4 + 9 * x pow 3 + c * x pow 2 + 9 * x + 4}
          in
            FINITE intersections /\ CARD intersections = 4)
       <=>
       c < 243 / 8)``;
