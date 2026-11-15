(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a6:
  for some n at least 1995, the number of 3 by n matrices whose columns are
  permutations of 1, 2, 3 and whose row sums are consecutive is at least four
  times the number whose row sums are all equal. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_1995_a6 =
  ``let admissible =
      \n : num.
      \M : int list list.
        LENGTH M = n /\
        EVERY
          (\column : int list.
             PERM column ([1; 2; 3] : int list))
          M
    in
    let row_sums =
      \M : int list list.
        {s : int |
           ?i : num.
             i < 3 /\
             s =
               FOLDR
                 (\column : int list.
                  \acc : int.
                    EL i column + acc)
                 0
                 M}
    in
    let sums_consecutive =
      \s : int set.
        s HAS_SIZE 3 /\
        ?a : int. s = {a; a + 1; a + 2}
    in
      ?n : num.
        1995 <= n /\
        4 *
          CARD
            {M : int list list |
               admissible n M /\ row_sums M HAS_SIZE 1}
        <=
        CARD
          {M : int list list |
             admissible n M /\ sums_consecutive (row_sums M)}``;
