(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a3:
  the least positive leading coefficient of an integer quadratic with two
  distinct real roots in the open unit interval is 5. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1967_a3 =
  ``let admissible =
      \a : num.
        0 < a /\
        ?b c : int. ?z1 z2 : real.
          0 < z1 /\ z1 < 1 /\
          0 < z2 /\ z2 < 1 /\
          z1 <> z2 /\
          (&a * z1 pow 2 + real_of_int b * z1 + real_of_int c = 0) /\
          (&a * z2 pow 2 + real_of_int b * z2 + real_of_int c = 0)
    in
      admissible 5 /\
      !a : num. admissible a ==> 5 <= a``;
