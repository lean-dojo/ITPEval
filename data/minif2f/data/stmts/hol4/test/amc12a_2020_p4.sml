(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p4: counting four-digit
  natural numbers whose decimal digits are even and which are divisible by 5. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val amc12a_2020_p4 =
  ``CARD
      {n : num |
         1000 <= n /\ n <= 9999 /\
         EVEN (n DIV 1000) /\
         EVEN ((n DIV 100) MOD 10) /\
         EVEN ((n DIV 10) MOD 10) /\
         EVEN (n MOD 10) /\
         divides 5 n} =
    100``;
