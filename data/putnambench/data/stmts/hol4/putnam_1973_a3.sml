(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a3:
  the minimum of k + n/k over positive integers k has the same integer part
  as sqrt (4n + 1) for every positive integer n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val putnam_1973_a3 =
  ``!b : int -> real.
      (!n : int.
         (!k : int.
            0 < k
            ==>
            b n <= real_of_int k + real_of_int n / real_of_int k) /\
         (?k : int.
            0 < k /\
            b n = real_of_int k + real_of_int n / real_of_int k))
      ==>
      !n : int.
        0 < n
        ==>
        INT_FLOOR (b n) =
          INT_FLOOR (sqrt (4 * real_of_int n + 1))``;
