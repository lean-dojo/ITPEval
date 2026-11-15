(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a1:
  the least area admitting positive rectangle sides that pack every positive
  real pair on the unit circle is (1 + sqrt 2) / 2. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_1996_a1 =
  ``let putnam_1996_a1_solution = (1 + sqrt 2) / 2
    in
    let packable =
      \n1 n2 a1 a2 : real.
        n1 + n2 <= max a1 a2 /\ max n1 n2 <= min a1 a2
    in
    let Aprop =
      \A : real.
        !n1 n2 : real.
          0 < n1 /\ 0 < n2 /\ n1 pow 2 + n2 pow 2 = 1
          ==>
          ?a1 a2 : real.
            0 < a1 /\ 0 < a2 /\ a1 * a2 = A /\
            packable n1 n2 a1 a2
    in
      Aprop putnam_1996_a1_solution /\
      (!A : real.
         Aprop A
         ==>
         putnam_1996_a1_solution <= A)``;
