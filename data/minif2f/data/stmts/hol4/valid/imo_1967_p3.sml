(*
  Statement-only formalization of miniF2F valid problem imo_1967_p3: divisibility between
  integer products of c(s) = s(s + 1) and their differences under a prime
  condition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val imo_1967_p3 =
  ``!k m n : num. !c : num -> num.
      0 < k /\ 0 < m /\ 0 < n /\
      (!s. c s = s * (s + 1)) /\
      prime (k + m + 1) /\
      n + 1 < k + m + 1
      ==>
      (ITSET
        (\i acc. int_of_num (c i) * acc)
        (IMAGE SUC (count n))
        (1 : int)) int_divides
        (ITSET
          (\i acc.
             (int_of_num (c (m + i)) - int_of_num (c k)) * acc)
          (IMAGE SUC (count n))
          (1 : int))``;
