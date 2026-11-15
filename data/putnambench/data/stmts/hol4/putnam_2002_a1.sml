(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a1:
  the numerator polynomial in the nth derivative of 1 / (x^k - 1),
  evaluated at x = 1, is (-k)^n times n factorial. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory polyTheory derivativeTheory;

val putnam_2002_a1 =
  ``let deriv0 =
      \f : real -> real.
        \x : real.
          if f differentiable (at x) then vector_derivative f (at x) else 0
    in
      !k : num. !P : num -> real list.
        0 < k /\
        (!n : num. !x : real.
           FUNPOW deriv0 n (\x' : real. 1 / (x' pow k - 1)) x =
             poly (P n) x / ((x pow k - 1) pow (n + 1)))
        ==>
        !n : num.
          poly (P n) 1 =
            (~(&k : real)) pow n * &(FACT n)``;
