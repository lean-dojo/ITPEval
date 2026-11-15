(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a1:
  no four consecutive binomial coefficients with positive starting index form
  an arithmetic progression. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory integerTheory;

val putnam_1972_a1 =
  ``let fourAP =
      \n1 n2 n3 n4 : int.
        n4 - n3 = n3 - n2 /\ n3 - n2 = n2 - n1
    in
      !n : num.
        0 < n
        ==>
        ~(?r : num.
            0 < r /\
            r + 3 <= n /\
            fourAP
              (int_of_num (binomial n r))
              (int_of_num (binomial n (r + 1)))
              (int_of_num (binomial n (r + 2)))
              (int_of_num (binomial n (r + 3))))``;
