(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b1:
  a degree-n polynomial with integer coefficients and a rational root has
  integer-valued partial Horner sums through every index below n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory ratTheory;

val putnam_2004_b1 =
  ``let rat_sum =
      \f : num -> rat.
      \N : num.
        ITSET
          (\k : num. \acc : rat. f k + acc)
          (count N)
          0q
    in
      !n : num. !c : num -> int. !r : rat.
        c n <> 0 /\
        (!k : num. n < k ==> c k = 0) /\
        rat_sum
          (\k : num. rat_of_int (c k) * rat_expn r k)
          (n + 1) = 0q
        ==>
        !i : num.
          i < n
          ==>
          ?m : int.
            rat_of_int m =
              rat_sum
                (\j : num.
                   rat_of_int (c (n - j)) *
                   rat_expn r (i + 1 - j))
                (i + 1)``;
