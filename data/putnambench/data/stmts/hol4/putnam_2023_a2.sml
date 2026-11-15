(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a2:
  the two additional real reciprocal interpolation points of a monic
  degree-2n polynomial prescribed at the nonzero integers through n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory realTheory intrealTheory
     polyTheory;

val putnam_2023_a2 =
  ``!n : num. !P : real list.
      let S =
        \x : real.
          ?k : int.
            x = real_of_int k /\
            1 <= Num (ABS k) /\
            Num (ABS k) <= n
      in
        0 < n /\
        EVEN n /\
        degree P = 2 * n /\
        LAST (normalize P) = 1 /\
        (!k : real.
           S k ==> poly P (1 / k) = k pow 2)
        ==>
        !x : real.
          (x <> 0 /\
           poly P (1 / x) = x pow 2 /\
           ~S x
           <=>
           x = 1 / &(FACT n) \/
           x = ~(1 / &(FACT n)))``;
