(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b6:
  a set of real square matrices satisfying exclusive signed closure and
  commute-or-anticommute conditions has at most n squared elements. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory fcpTheory realTheory real_sigmaTheory;
open matrixTheory;

val putnam_1992_b6 =
  ``!n : num. !M : real['N]['N] set.
      0 < n /\
      dimindex (:'N) = n /\
      matrix$mat 1 IN M /\
      (!A B : real['N]['N].
         A IN M /\ B IN M
         ==>
         ((A ** B IN M) <> ((~A) ** B IN M))) /\
      (!A B : real['N]['N].
         A IN M /\ B IN M
         ==>
         A ** B = B ** A \/ A ** B = (~B) ** A) /\
      (!A : real['N]['N].
         A IN M /\ A <> matrix$mat 1
         ==>
         ?B : real['N]['N].
           B IN M /\ A ** B = (~B) ** A)
      ==>
      FINITE M /\ CARD M <= n EXP 2``;
