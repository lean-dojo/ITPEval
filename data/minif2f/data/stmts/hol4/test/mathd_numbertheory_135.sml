(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_135:
  determining the three-digit number ABC from the decimal expansion ABCACCBAB
  of 3^17 + 3^10 and digit constraints. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_135 =
  ``!n A B C : num.
      n = 3 EXP 17 + 3 EXP 10 /\
      divides 11 (n + 1) /\
      A <> B /\ B <> C /\ A <> C /\
      A <= 9 /\ B <= 9 /\ C <= 9 /\
      ODD A /\ ODD C /\
      ~(divides 3 B) /\
      n =
        10 *
          (10 *
            (10 *
              (10 *
                (10 *
                  (10 *
                    (10 * (10 * A + B) + C) + A) +
                   C) +
                 C) +
               B) +
             A) +
           B
      ==>
      100 * A + 10 * B + C = 129``;
