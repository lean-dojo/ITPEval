(*
  Statement-only formalization of miniF2F valid problem amc12a_2020_p21: counting natural
  numbers divisible by 5 whose LCM with 5! is five times their GCD with 10!. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory pred_setTheory;

val amc12a_2020_p21 =
  ``FINITE
      {n : num |
         divides 5 n /\
         lcm (FACT 5) n = 5 * gcd (FACT 10) n} /\
    CARD
      {n : num |
         divides 5 n /\
         lcm (FACT 5) n = 5 * gcd (FACT 10) n} =
      48``;
