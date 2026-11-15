(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a2:
  a strictly increasing positive integer-valued function that fixes two and
  is multiplicative on coprime positive inputs is the identity on the positive
  integers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val putnam_1963_a2 =
  ``!f : num -> num.
      (!n : num. 0 < f n) /\
      (!i j : num.
         0 < i /\ i < j
         ==>
         f i < f j) /\
      f 2 = 2 /\
      (!m n : num.
         0 < m /\ 0 < n /\ coprime m n
         ==>
         f (m * n) = f m * f n)
      ==>
      !n : num.
        0 < n
        ==>
        f n = n``;
