(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b4:
  symmetry in the number of fixed-length integer tuples whose sum of absolute
  values is bounded by a positive integer. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_2005_b4 =
  ``!m n : num. !f : num -> num -> num.
      (0 < m /\
       0 < n /\
       (!m' n' : num.
          0 < m' /\ 0 < n'
          ==>
          f m' n' =
          CARD
            {x : int list |
               LENGTH x = n' /\
               SUM (MAP (\z : int. Num (ABS z)) x) <= m'})
      ==>
      f m n = f n m)``;
