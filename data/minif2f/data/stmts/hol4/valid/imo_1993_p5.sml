(*
  Statement-only formalization of miniF2F valid problem imo_1993_p5: existence of a
  strictly increasing natural-number function satisfying f(1) = 2 and
  f(f(n)) = f(n) + n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val imo_1993_p5 =
  ``?f : num -> num.
      f 1 = 2 /\
      (!n. f (f n) = f n + n) /\
      (!n m. n < m ==> f n < f m)``;
