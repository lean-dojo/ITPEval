(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b4:
  the recurrence and pointwise convergence set and limit of a ratio of
  even- and odd-indexed binomial sums. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory
     real_sigmaTheory;
open real_topologyTheory;

val putnam_1965_b4 =
  ``!f u v : num -> real -> real. !n : num.
      (!m : num. 0 < m ==>
         !x : real.
           u m x =
           SIGMA
             (\i : num.
                (&(binomial m (2 * i)) : real) * x pow i)
             (count (m DIV 2 + 1))) /\
      (!m : num. 0 < m ==>
         !x : real.
           v m x =
           SIGMA
             (\i : num.
                (&(binomial m (2 * i + 1)) : real) * x pow i)
             (count ((m - 1) DIV 2 + 1))) /\
      (!m : num. 0 < m ==>
         !x : real. f m x = u m x / v m x) /\
      0 < n
      ==>
      (!x : real.
         v n x <> 0 /\
         v (n + 1) x <> 0 /\
         f n x + 1 <> 0
         ==>
         f (n + 1) x = (f n x + x) / (f n x + 1)) /\
      {x : real |
         ?l : real.
           (((\m : num. f m x) --> l) sequentially)} =
        {x : real | 0 <= x} /\
      !x : real.
        0 <= x
        ==>
        (((\m : num. f m x) --> sqrt x) sequentially)``;
