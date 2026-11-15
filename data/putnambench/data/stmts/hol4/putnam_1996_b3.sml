(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b3:
  the largest cyclic sum of adjacent products over permutations of the
  integers from 1 through n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1996_b3 =
  ``!n : num.
      2 <= n
      ==>
      let values = IMAGE SUC (count n)
      in
      let cyclic_sum =
        \x : num -> num.
          SIGMA
            (\i : num. x i * x ((i + 1) MOD n))
            (count n)
      in
      let solution =
        (2 * n ** 3 + 3 * n ** 2 + 18 - 11 * n) DIV 6
      in
        (?x : num -> num.
           IMAGE x (count n) = values /\
           cyclic_sum x = solution) /\
        (!x : num -> num.
           IMAGE x (count n) = values
           ==>
           cyclic_sum x <= solution)``;
