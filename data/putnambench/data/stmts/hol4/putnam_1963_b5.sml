(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b5:
  convergence to zero of n * a_n for an integer-indexed real sequence whose
  natural partial-sum series converges and whose terms on each interval
  [n, 2n] satisfy the stated nonnegativity and comparison bounds.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1963_b5 =
  ``!a : int -> real.
      (!n k : int.
         1 <= n /\ n <= k /\ k <= 2 * n
         ==>
         0 <= a k /\ a k <= 100 * a n) /\
      (?S : real.
         ((\N : num.
             SIGMA
               (\j : num. a (int_of_num j))
               (count N)) --> S) sequentially)
      ==>
      ((\n : num. &n * a (int_of_num n)) --> 0) sequentially``;
