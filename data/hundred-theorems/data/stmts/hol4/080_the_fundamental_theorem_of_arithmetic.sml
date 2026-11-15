(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__080, cataloged as "The Fundamental Theorem of
  Arithmetic": every nonzero natural number has a unique finitely supported
  assignment of natural exponents to primes whose prime-power product is that
  number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val fundamental_theorem_of_arithmetic =
  ``!n : num.
      n <> 0 ==>
      ?!exponent : num -> num.
        FINITE {p : num | exponent p <> 0} /\
        (!p : num. exponent p <> 0 ==> prime p) /\
        n =
          PROD_IMAGE
            (\p : num. p EXP exponent p)
            {p : num | exponent p <> 0}``;
