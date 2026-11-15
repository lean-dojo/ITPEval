(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b3:
  the least positive uniform upper bound for the minima of
  |c - d * sqrt 3| over nonnegative integer pairs with fixed positive sum is
  (1 + sqrt 3) / 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val putnam_1988_b3 =
  ``!r : int -> real.
      (!n : int.
         1 <= n
         ==>
         (?c d : int.
            0 <= c /\ 0 <= d /\ c + d = n /\
            r n =
              abs
                (real_of_int c -
                 real_of_int d * sqrt 3)) /\
         (!c d : int.
            0 <= c /\ 0 <= d /\ c + d = n
            ==>
            r n <=
              abs
                (real_of_int c -
                 real_of_int d * sqrt 3)))
      ==>
      let solution = (1 + sqrt 3) / 2
      in
        0 < solution /\
        (!n : int. 1 <= n ==> r n <= solution) /\
        (!g : real.
           0 < g /\
           (!n : int. 1 <= n ==> r n <= g)
           ==>
           solution <= g)``;
