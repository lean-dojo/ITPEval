(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b4:
  toggling each numbered locker once for every divisor leaves exactly the
  perfect-square-numbered lockers open. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val putnam_1967_b4 =
  ``!n : num. !lockers : num -> num -> bool.
      1 <= n /\
      (!i : num.
         1 <= i /\ i <= n
         ==>
         lockers 0 i = F) /\
      (!k i : num.
         1 <= k /\ k <= n /\
         1 <= i /\ i <= n
         ==>
         lockers k i =
           if divides k i then
             ~(lockers (k - 1) i)
           else
             lockers (k - 1) i)
      ==>
      !i : num.
        1 <= i /\ i <= n
        ==>
        (lockers n i <=> ?j : num. j EXP 2 = i)``;
