(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a2:
  the determinant of the intersection-incidence matrix of all nonempty
  subsets of {1, ..., n} is 1 for n = 1 and -1 otherwise. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory;

val putnam_2018_a2 =
  ``let determinant =
      \m : num. \A : num -> num -> real.
        ITSET
          (\p : num -> num. \sum : real.
             (if evenperm p then
                ITSET
                  (\i : num. \acc : real. A i (p i) * acc)
                  (count m)
                  1
              else
                -(ITSET
                    (\i : num. \acc : real. A i (p i) * acc)
                    (count m)
                    1)) +
             sum)
          {p : num -> num | p permutes count m}
          0
    in
      !n : num. !S : num -> num set. !M : num -> num -> real.
        1 <= n /\
        IMAGE S (count (2 EXP n - 1)) =
          (POW (IMAGE SUC (count n))) DELETE EMPTY /\
        (!i j : num.
           i < 2 EXP n - 1 /\ j < 2 EXP n - 1
           ==>
           M i j = if DISJOINT (S i) (S j) then 0 else 1)
        ==>
        determinant (2 EXP n - 1) M =
          if n = 1 then 1 else -1``;
