(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b5:
  finite sets of positive integers evolving by adjacent-membership
  exclusive-or recur arbitrarily often as the union of the initial set and
  its translate by the time index. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2000_b5 =
  ``!S : num -> int set.
      (!n : num. FINITE (S n)) /\
      (!n : num. !s : int. s IN S n ==> 0 < s) /\
      (!n : num. !a : int.
         a IN S (n + 1) <=>
         (((a - 1) IN S n) <> (a IN S n)))
      ==>
      !n : num.
        ?N : num.
          n <= N /\
          S N =
            S 0 UNION
            {M : int | M - int_of_num N IN S 0}``;
