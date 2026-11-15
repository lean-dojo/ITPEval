(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b6:
  the largest bound on a real parameter for a weighted hyperbolic-sine
  inequality between positive real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_1991_b6 =
  ``!a b : real.
      0 < a /\ 0 < b
      ==>
      let sinh =
        \z : real. (exp z - exp (~z)) / 2
      in
      let admissible =
        \c : real.
          !u : real.
            0 < abs u /\ abs u <= c
            ==>
            !x : real.
              0 < x /\ x < 1
              ==>
              a powr x * b powr (1 - x) <=
                a * (sinh (u * x) / sinh u) +
                b * (sinh (u * (1 - x)) / sinh u)
      in
      let solution = abs (ln (a / b))
      in
        admissible solution /\
        !c : real. admissible c ==> c <= solution``;
