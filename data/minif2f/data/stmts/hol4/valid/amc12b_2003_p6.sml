(*
  Statement-only formalization of miniF2F valid problem amc12b_2003_p6: the first term of a
  real geometric sequence with specified first and third indexed values. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12b_2003_p6 =
  ``!a r : real. !u : num -> real.
      (!k : num. u k = a * r pow k) /\
      u 1 = 2 /\
      u 3 = 6
      ==>
      u 0 = 2 / sqrt 3 \/ u 0 = ~(2 / sqrt 3)``;
