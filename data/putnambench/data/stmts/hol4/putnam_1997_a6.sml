(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a6:
  the recursively defined real sequence at the largest root of its terminal
  term has binomial-coefficient values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory realTheory;

val putnam_1997_a6 =
  ``!n : num. !x : real -> num -> real. !C : real.
      0 < n /\
      (!c : real. x c 0 = 0) /\
      (!c : real. x c 1 = 1) /\
      (!c : real. !k : num.
         x c (k + 2) =
           (c * x c (k + 1) - &(n - k) * x c k) / &(k + 1)) /\
      x C (n + 1) = 0 /\
      (!c : real. x c (n + 1) = 0 ==> c <= C)
      ==>
      !k : num.
        1 <= k /\ k <= n
        ==>
        x C k = (&(binomial (n - 1) (k - 1)) : real)``;
