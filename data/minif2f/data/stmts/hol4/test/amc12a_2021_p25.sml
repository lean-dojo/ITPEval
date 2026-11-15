(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p25: the decimal digits
  of the unique positive-natural maximizer of divisor count divided by real cube root sum to
  9. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory listTheory numposrepTheory pred_setTheory
     realTheory transcTheory;

val amc12a_2021_p25 =
  ``!N : num. !f : num -> real.
      0 < N /\
      (!n : num.
         0 < n ==>
         f n =
           &(CARD {d : num | 0 < d /\ d <= n /\ divides d n}) /
           ((&n : real) powr (1 / 3))) /\
      (!n : num. ~(n = N) /\ 0 < n ==> f n < f N)
      ==>
      SUM (num_to_dec_list N) = 9``;
