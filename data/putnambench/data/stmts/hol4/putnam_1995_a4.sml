(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a4:
  an integer-labelled cyclic necklace with total label sum n - 1 has a cut
  whose every nonempty prefix sum is at most its zero-based endpoint. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1995_a4 =
  ``!n : num. !necklace : num -> int.
      0 < n /\
      ITSET
        (\i : num. \acc : int. necklace i + acc)
        (count n)
        0 =
        int_of_num n - 1
      ==>
      ?cut : num.
        cut < n /\
        !k : num.
          k < n
          ==>
          ITSET
            (\i : num. \acc : int.
               necklace ((cut + i) MOD n) + acc)
            (count (SUC k))
            0 <=
          int_of_num k``;
