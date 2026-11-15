(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a5:
  the maximum magnitude of the derivative at zero among real quadratic
  polynomials bounded in magnitude by one on [0,1] is 8. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1968_a5 =
  ``let admissible =
      \a b c : real.
        a <> 0 /\
        !x : real.
          0 <= x /\ x <= 1
          ==>
          abs (a * x pow 2 + b * x + c) <= 1
    in
      (?a b c : real.
         admissible a b c /\
         abs b = 8) /\
      (!a b c : real.
         admissible a b c
         ==>
         abs b <= 8)``;
