(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b6
  (putnambench__hol4__putnam_2025_b6): the greatest real exponent admitting
  a natural-number function positive on positive inputs whose successive growth
  dominates the corresponding real power of its self-composition. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val putnam_2025_b6 =
  ``let admissible =
      \r : real.
        ?g : num -> num.
          (!n : num. 0 < n ==> 0 < g n) /\
          !n : num.
            0 < n
            ==>
            (&(g (g n)) : real) powr r <=
              (&(g (n + 1)) : real) - &(g n)
    in
    let solution = (1 / 4 : real)
    in
      admissible solution /\
      !r : real. admissible r ==> r <= solution``;
