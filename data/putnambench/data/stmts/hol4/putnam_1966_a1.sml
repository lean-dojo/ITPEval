(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a1:
  the product of positive integers x > y equals the difference of two
  partial sums of the sequence 0, 1, 1, 2, 2, 3, and so on.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1966_a1 =
  ``let f =
      \n : int.
        SIGMA
          (\m : num. int_of_num (m DIV 2))
          (count (SUC (Num n)))
    in
      !x y : int.
        0 < x /\ 0 < y /\ y < x
        ==>
        x * y = f (x + y) - f (x - y)``;
