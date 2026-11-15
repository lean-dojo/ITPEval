(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b3:
  consecutive positive solutions of tan x = x have gaps exceeding pi by a
  positive amount bounded above by 1 / ((n^2 + n) * pi). This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val putnam_2024_b3 =
  ``!r : num -> real.
      (!m n : num.
         0 < m /\ 0 < n /\ m < n
         ==>
         r m < r n) /\
      (!x : real.
         0 < x /\ x < r 1
         ==>
         tan x <> x) /\
      (!k : num.
         0 < k
         ==>
         0 < r k /\
         tan (r k) = r k /\
         !x : real.
           r k < x /\ x < r (k + 1)
           ==>
           tan x <> x)
      ==>
      !n : num.
        0 < n
        ==>
        0 < r (n + 1) - r n - pi /\
        r (n + 1) - r n - pi <
          1 / (&(n EXP 2 + n) * pi)``;
