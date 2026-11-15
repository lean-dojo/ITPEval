(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a3:
  the number of intersection-preserving functions from the subsets of
  {1,...,n} to {1,...,m} equals the sum of the nth powers from 1 to m. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1993_a3 =
  ``let pown =
      \n : num. POW (IMAGE SUC (count n))
    in
    let c =
      \n m : num.
        CARD
          {f : num set -> num |
             (!s : num set.
                s IN pown n
                ==>
                f s IN IMAGE SUC (count m)) /\
             (!s : num set.
                s NOTIN pown n
                ==>
                f s = 0) /\
             (!A B : num set.
                A IN pown n /\ B IN pown n
                ==>
                f (A INTER B) = MIN (f A) (f B))}
    in
      !n m : num.
        1 <= n /\ 1 <= m
        ==>
        c n m =
          SIGMA
            (\j : num. j EXP n)
            (IMAGE SUC (count m))``;
