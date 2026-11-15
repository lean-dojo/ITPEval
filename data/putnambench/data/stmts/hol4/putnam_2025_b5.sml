(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b5
  (putnambench__hol4__putnam_2025_b5): for every prime p greater than 3, the
  least positive modular inverses modulo p have more than p/4 - 1 descents on
  the indices from 1 through p - 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_2025_b5 =
  ``let mod_inv =
      \p : num. \k : num.
        @i : num. i < p /\ (k * i) MOD p = 1
    in
      !p : num.
        prime p /\ 3 < p
        ==>
        p <
          4 *
          (CARD
             {k : num |
                1 <= k /\
                k <= p - 2 /\
                mod_inv p (k + 1) < mod_inv p k} +
           1)``;
