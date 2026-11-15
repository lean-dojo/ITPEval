(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/euler001_Euler001_solveqtvc: the Euler problem 1 verification
  condition equating the sum of nonnegative multiples of 3 or 5 below a
  positive integer with its inclusion-exclusion quotient formula. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val euler001_Euler001_solve_vc =
  ``!sum_multiple_3_5_lt : int -> int.
      sum_multiple_3_5_lt (0 : int) = (0 : int) ==>
      (!k : int.
         (0 : int) <= k ==>
         ~(k rem (3 : int) = (0 : int)) ==>
         ~(k rem (5 : int) = (0 : int)) ==>
         sum_multiple_3_5_lt (k + (1 : int)) =
           sum_multiple_3_5_lt k) ==>
      (!k : int.
         (0 : int) <= k ==>
         (k rem (3 : int) = (0 : int) \/
          k rem (5 : int) = (0 : int)) ==>
         sum_multiple_3_5_lt (k + (1 : int)) =
           sum_multiple_3_5_lt k + k) ==>
      !n : int.
        (1 : int) <= n ==>
        ~((3 : int) = (0 : int)) /\
        (let n3 = (n - (1 : int)) quot (3 : int)
         in
           ~((5 : int) = (0 : int)) /\
           (let n5 = (n - (1 : int)) quot (5 : int)
            in
              ~((15 : int) = (0 : int)) /\
              (let n15 = (n - (1 : int)) quot (15 : int)
               in
                 ~((2 : int) = (0 : int)) /\
                 (((3 : int) * n3 * (n3 + (1 : int)) +
                   (5 : int) * n5 * (n5 + (1 : int)) -
                   (15 : int) * n15 * (n15 + (1 : int)))
                    quot (2 : int) =
                  sum_multiple_3_5_lt n))))``;
