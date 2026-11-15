(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b3:
  the positive indices where the count of average-closed subsets has second
  finite difference one are exactly one less than positive powers of two.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2009_b3 =
  ``let mediocre =
      \n : num.
      \S : num set.
        S SUBSET {m : num | 1 <= m /\ m <= n} /\
        !a b : num.
          a IN S /\ b IN S /\ EVEN (a + b)
          ==>
          (a + b) DIV 2 IN S
    in
    let A =
      \n : num.
        int_of_num
          (CARD {s : num set | mediocre n s})
    in
      {n : num |
         0 < n /\
         A (n + 2) - 2 * A (n + 1) + A n = 1} =
      {n : num |
         ?k : num.
           1 <= k /\ n = 2 EXP k - 1}``;
