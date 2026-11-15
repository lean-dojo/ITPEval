(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b4:
  an alternating floor-quotient sum for two positive integers vanishes exactly
  when their 2-adic valuations differ. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory pred_setTheory;

val putnam_1998_b4 =
  ``let exact_power_of_two_divisor =
      \k x : num.
        divides (2 EXP k) x /\
        ~(divides (2 EXP (k + 1)) x)
    in
      !m n : num.
        0 < m /\ 0 < n
        ==>
        (ITSET
           (\i : num. \acc : int.
              (if EVEN (i DIV m + i DIV n) then 1 else ~1) + acc)
           (count (m * n))
           0 =
         0
         <=>
         ?a b : num.
           exact_power_of_two_divisor a m /\
           exact_power_of_two_divisor b n /\
           a <> b)``;
