(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_a4:
  a real-coefficient polynomial in three variables with the stated scaling
  identity and axis values determines the distance from A to C at a complex
  zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory
     complexTheory;

val putnam_1987_a4 =
  ``let support =
      \P : num # (num # num) -> complex.
        {ijk : num # (num # num) | P ijk <> 0}
    in
    let polynomial =
      \P : num # (num # num) -> complex.
        FINITE (support P)
    in
    let eval =
      \P : num # (num # num) -> complex.
      \x y z : complex.
        ITSET
          (\ijk acc.
             P ijk *
             x pow (FST ijk) *
             y pow (FST (SND ijk)) *
             z pow (SND (SND ijk)) +
             acc)
          (support P)
          (0 : complex)
    in
    let putnam_1987_a4_solution = (5 / 3) * sqrt 30
    in
      !P : num # (num # num) -> complex.
      !F : real -> real -> real.
      !A B C : complex.
        polynomial P /\
        (!ijk : num # (num # num). IM (P ijk) = 0) /\
        (!x y z u : real.
           eval P
             (complex_of_real (u * x))
             (complex_of_real (u * y))
             (complex_of_real (u * z)) =
           complex_of_real (u pow 2 * F (y - x) (z - x))) /\
        eval P 1 0 0 = 4 /\
        eval P 0 1 0 = 5 /\
        eval P 0 0 1 = 6 /\
        eval P A B C = 0 /\
        modu (B - A) = 10
        ==>
        modu (C - A) = putnam_1987_a4_solution``;
