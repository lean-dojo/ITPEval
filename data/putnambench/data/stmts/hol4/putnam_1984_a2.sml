(*
  Statement-only formalization of PutnamBench artifact putnam_1984_a2:
  the infinite series with kth term
  6^k / ((3^(k+1) - 2^(k+1)) * (3^k - 2^k)), for k starting at 1,
  converges to 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_1984_a2 =
  ``(\n : num.
       (6 : real) pow (n + 1) /
       (((3 : real) pow (n + 2) - (2 : real) pow (n + 2)) *
        ((3 : real) pow (n + 1) - (2 : real) pow (n + 1))))
    sums (2 : real)``;
