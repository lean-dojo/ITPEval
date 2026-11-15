(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p12: a monic degree-six
  complex polynomial whose zeros are positive integers determines its cubic coefficient. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory intrealTheory complexTheory;

val amc12a_2021_p12 =
  ``!a b c d : real. !f : complex -> complex.
      (!z : complex.
         f z =
           z pow 6 - 10 * z pow 5 +
           complex_of_real a * z pow 4 +
           complex_of_real b * z pow 3 +
           complex_of_real c * z pow 2 +
           complex_of_real d * z + 16) /\
      (!z : complex.
         f z = 0 ==>
         IM z = 0 /\
         0 < RE z /\
         real_of_int (INT_FLOOR (RE z)) = RE z)
      ==>
      b = -88``;
