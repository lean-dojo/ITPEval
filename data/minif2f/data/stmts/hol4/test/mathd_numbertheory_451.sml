(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_451:
  summing the numbers from 2010 through 2019 that are divisor sums of naturals
  with exactly four divisors. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val _ = new_theory "hello";

val mathd_numbertheory_451 =
  ``!S : num set.
      FINITE S /\
      (!n : num.
         n IN S <=>
         2010 <= n /\ n <= 2019 /\
         (?m : num.
            0 < m /\
            CARD {p : num | divides p m} = 4 /\
            SIGMA (\p : num. p) {p : num | divides p m} = n))
      ==>
      SIGMA (\k : num. k) S = 2016``;

val _ = export_theory();
