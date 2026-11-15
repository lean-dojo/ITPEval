(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b2:
  recursively defined polynomials have f_100(1) equal to 101^99, giving its
  explicit prime factorization. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory polyTheory;

val putnam_1985_b2 =
  ``!(f : num -> real list).
      (!x : real. poly (f 0) x = 1) /\
      (!n : num. 1 <= n ==> poly (f n) 0 = 0) /\
      (!n : num. !x : real.
         poly (diff (f (SUC n))) x =
           &(SUC n) * poly (f n) (x + 1))
      ==>
      poly (f 100) 1 = &(101 EXP 99)``;
