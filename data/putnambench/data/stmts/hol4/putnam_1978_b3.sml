(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b3:
  recursively defined real polynomials have largest real roots that increase
  strictly and converge to zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory polyTheory;

val putnam_1978_b3 =
  ``!P : num -> real list. !a : num -> real.
      P 1 = [1; 1] /\
      P 2 = [1; 2] /\
      (!n : num.
         1 <= n
         ==>
         P (2 * n + 1) =
           P (2 * n) + ([0; &(n + 1)] : real list) * P (2 * n - 1)) /\
      (!n : num.
         1 <= n
         ==>
         P (2 * n + 2) =
           P (2 * n + 1) + ([0; &(n + 1)] : real list) * P (2 * n)) /\
      (!n : num. 1 <= n ==> poly (P n) (a n) = 0) /\
      (!n : num. !x : real.
         1 <= n /\ poly (P n) x = 0
         ==>
         x <= a n)
      ==>
      ((!i j : num.
          1 <= i /\ i < j
          ==>
          a i < a j) /\
       (a --> 0) sequentially)``;
