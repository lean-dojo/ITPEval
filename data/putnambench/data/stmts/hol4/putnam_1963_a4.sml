(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a4:
  the extended-real limit superior bound for a sequence derived from any
  positive real sequence, together with the sharpness of the bound one.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory extrealTheory;

val putnam_1963_a4 =
  ``let T =
      \a : num -> real.
      \n : num.
        Normal (&n * ((1 + a (SUC n)) / a n - 1))
    in
      (!a : num -> real.
         (!n : num. 0 < a n)
         ==>
         Normal 1 <= limsup (T a)) /\
      (!C : real.
         1 < C
         ==>
         ?a : num -> real.
           (!n : num. 0 < a n) /\
           ~(Normal C <= limsup (T a)))``;
