(*
  Statement-only formalization of miniF2F test problem amc12a_2013_p4: evaluation of a
  quotient of real powers of 2 as 5 / 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2013_p4 =
  ``((2 : real) pow 2014 + 2 pow 2012) /
      (2 pow 2014 - 2 pow 2012) =
    5 / 3``;
