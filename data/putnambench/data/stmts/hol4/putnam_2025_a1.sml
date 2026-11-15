(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a1:
  positive integer sequences satisfying the given rational recurrence have
  only finitely many indices at which their doubled-plus-one terms are not
  relatively prime. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory pred_setTheory ratTheory;

val putnam_2025_a1 =
  ``!m n : num -> num.
      (!k : num. 0 < m k) /\
      (!k : num. 0 < n k) /\
      m 0 <> n 0 /\
      (!k : num. 0 < k ==> coprime (m k) (n k)) /\
      (!k : num.
         rat_of_num (m (k + 1)) / rat_of_num (n (k + 1)) =
           (2 * rat_of_num (m k) + 1) /
           (2 * rat_of_num (n k) + 1))
      ==>
      FINITE
        {k : num |
           ~coprime (2 * m k + 1) (2 * n k + 1)}``;
