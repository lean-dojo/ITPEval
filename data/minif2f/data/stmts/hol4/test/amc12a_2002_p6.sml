(*
  Statement-only formalization of miniF2F test problem amc12a_2002_p6: every positive natural
  number has a larger natural number m for which some natural p satisfies m * p <= m + p.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val amc12a_2002_p6 =
  ``!n : num.
      0 < n ==>
      ?m : num. m > n /\ ?p : num. m * p <= m + p``;
