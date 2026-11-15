(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a5:
  two distinct real roots of a cubic have floor-multiple sequences with
  unboundedly many common integer values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1979_a5 =
  ``!S : real -> num -> int. !P : real -> bool.
      S = (\x : real. \n : num. INT_FLOOR ((&n : real) * x)) /\
      (!x : real.
         P x <=>
         x pow 3 - 10 * x pow 2 + 29 * x - 25 = 0)
      ==>
      ?alpha beta : real.
        alpha <> beta /\
        P alpha /\
        P beta /\
        !n : num.
          ?m : int.
            int_of_num n < m /\
            ?c d : num.
              S alpha c = m /\
              S beta d = m``;
