(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b4:
  the expected determinant of A minus its transpose for a uniformly random
  2n by 2n zero-one matrix is (2n)! divided by 4^n n!. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory fcpTheory permutesTheory realTheory
     real_sigmaTheory;

val putnam_2016_b4 =
  ``let determinant =
      \M : real['N]['N].
        ITSET
          (\p : num -> num. \sum : real.
             (if evenperm p then
                ITSET
                  (\i : num. \acc : real. M ' i ' (p i) * acc)
                  (count (dimindex (:'N)))
                  1
              else
                -(ITSET
                    (\i : num. \acc : real. M ' i ' (p i) * acc)
                    (count (dimindex (:'N)))
                    1)) +
             sum)
          {p : num -> num | p permutes count (dimindex (:'N))}
          0
    in
    let mats01 =
      {A : real['N]['N] |
         !i j : num.
           i < dimindex (:'N) /\
           j < dimindex (:'N)
           ==>
           A ' i ' j = 0 \/ A ' i ' j = 1}
    in
      !n : num.
        1 <= n /\
        dimindex (:'N) = 2 * n
        ==>
        SIGMA
          (\A : real['N]['N].
             determinant
               (FCP i j. A ' i ' j - A ' j ' i))
          mats01 /
          (&(CARD mats01) : real) =
        (&(FACT (2 * n)) : real) /
          (4 pow n * &(FACT n))``;
