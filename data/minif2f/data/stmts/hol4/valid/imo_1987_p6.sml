(*
  Statement-only formalization of miniF2F valid problem imo_1987_p6: propagation of
  primality for the natural-number quadratic f(k) = k^2 + k + p from indices through
  floor(sqrt(p/3)) to every index at most p - 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory logrootTheory;

val imo_1987_p6 =
  ``!p : num. !f : num -> num.
      (!x. f x = x EXP 2 + x + p) /\
      (!k. k <= SQRT (p DIV 3) ==> prime (f k))
      ==>
      !i. i <= p - 2 ==> prime (f i)``;
