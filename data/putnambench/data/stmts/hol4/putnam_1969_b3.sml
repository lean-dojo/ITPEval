(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b3:
  a real sequence whose adjacent terms have product n for every n >= 1
  and whose successive-term ratio tends to 1 satisfies pi * T_1^2 = 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory transcTheory;

val putnam_1969_b3 =
  ``!T : num -> real.
      (!n : num.
         1 <= n
         ==>
         T n * T (n + 1) = &n) /\
      ((\n : num. T n / T (n + 1)) --> 1) sequentially
      ==>
      pi * (T 1) pow 2 = 2``;
