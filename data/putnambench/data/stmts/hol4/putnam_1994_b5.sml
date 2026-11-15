(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b5:
  existence of a real parameter whose floor map and its iterates send n squared
  to n squared minus k for every k from one through n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1994_b5 =
  ``!n : num. !f : real -> int -> int.
      0 < n /\
      (!alpha : real. !x : int.
         f alpha x = INT_FLOOR (alpha * real_of_int x))
      ==>
      ?alpha : real.
        !k : num.
          1 <= k /\ k <= n
          ==>
          FUNPOW (f alpha) k (int_of_num (n EXP 2)) =
            int_of_num (n EXP 2 - k) /\
          f (alpha pow k) (int_of_num (n EXP 2)) =
            int_of_num (n EXP 2 - k)``;
