(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b2:
  the asymptotic count of positive integers whose distance from a nearest
  perfect square is itself a perfect square. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory;
open real_topologyTheory transcTheory;

val putnam_2016_b2 =
  ``let is_square =
      \n : num. ?m : num. n = m EXP 2;
      square_distance =
        \n : num. \m : num.
          Num (ABS (int_of_num n - int_of_num (m EXP 2)));
      squarish =
        \n : num.
          is_square n \/
          ?w : num.
            is_square (square_distance n w) /\
            !v : num. square_distance n w <= square_distance n v;
      S =
        \N : num.
          CARD
            {n : num |
               n IN IMAGE SUC (count N) /\
               squarish n};
      p =
        \alpha : real. \beta : real.
          0 < alpha /\
          0 < beta /\
          (((\N : num.
               (&(S N) : real) / ((&N : real) powr alpha)) --> beta)
            sequentially);
      solution = ((3 / 4 : real), (4 / 3 : real))
    in
      (!alpha beta : real.
         ((alpha, beta) = solution <=> p alpha beta)) \/
      (!alpha beta : real. ~(p alpha beta))``;
