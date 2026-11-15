(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b6:
  a finite group of positive-dimensional real square matrices with zero total
  trace has zero matrix sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory fcpTheory realTheory real_sigmaTheory;
open matrixTheory;

val putnam_1985_b6 =
  ``let matrix_trace =
      \A : real['N]['N].
        SIGMA
          (\i : num. A ' i ' i)
          (count (dimindex (:'N)))
    in
    let matrix_sum =
      \G : real['N]['N] set.
        ITSET
          (\A acc. matrix$matrix_add A acc)
          G
          (matrix$mat 0)
    in
      !n : num. !G : real['N]['N] set.
        0 < n /\
        dimindex (:'N) = n /\
        FINITE G /\
        (!A : real['N]['N].
           A IN G
           ==>
           !B : real['N]['N].
             B IN G
             ==>
             matrix$matrix_mul A B IN G) /\
        matrix$mat 1 IN G /\
        (!A : real['N]['N].
           A IN G
           ==>
           ?B : real['N]['N].
             B IN G /\
             matrix$matrix_mul A B = matrix$mat 1) /\
        SIGMA matrix_trace G = 0
        ==>
        matrix_sum G = matrix$mat 0``;
