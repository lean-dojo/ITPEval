(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b4:
  the minimum distance from a real number to values sqrt(m^2 + 2*n^2), for
  integers m and n, tends to zero at positive infinity. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory real_topologyTheory limTheory
     transcTheory;

val putnam_1986_b4 =
  ``!G : real -> real.
      (!r : real.
         ?m n : int.
           G r =
             abs
               (r -
                sqrt
                  (real_of_int
                     (m ** 2 + 2 * n ** 2)))) /\
      (!r : real.
         !m n : int.
           G r <=
             abs
               (r -
                sqrt
                  (real_of_int
                     (m ** 2 + 2 * n ** 2))))
      ==>
      (G --> 0) at_posinfinity``;
