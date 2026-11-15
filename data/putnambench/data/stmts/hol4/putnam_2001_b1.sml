(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b1:
  equal sums in the two color classes of a row-major numbered even square
  grid when each row and column contains equally many squares of each color.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2001_b1 =
  ``!n : num.
      !nums : num -> num -> int.
      !colors : num -> num -> bool.
        0 < n /\
        EVEN n /\
        (!k l : num.
           k < n /\ l < n
           ==>
           nums k l = int_of_num (k * n + l + 1)) /\
        (!k : num.
           k < n
           ==>
           CARD {l : num | l < n /\ ~colors k l} = n DIV 2) /\
        (!l : num.
           l < n
           ==>
           CARD {k : num | k < n /\ ~colors k l} = n DIV 2)
        ==>
        ITSET
          (\k : num. \total : int.
             ITSET
               (\l : num. \row_total : int.
                  (if ~colors k l then nums k l else 0) + row_total)
               (count n)
               0 +
             total)
          (count n)
          0 =
        ITSET
          (\k : num. \total : int.
             ITSET
               (\l : num. \row_total : int.
                  (if colors k l then nums k l else 0) + row_total)
               (count n)
               0 +
             total)
          (count n)
          0``;
