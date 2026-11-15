(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b4:
  an integer-coefficient quartic with four real roots has rational pair-product
  when the corresponding pair-sum is rational and differs from the other
  pair-sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val putnam_2003_b4 =
  ``let rational =
      \x : real.
        ?p q : int.
          q <> 0 /\
          x = real_of_int p / real_of_int q
    in
      !a b c d e : int. !r1 r2 r3 r4 : real.
        a <> 0 /\
        (!z : real.
           real_of_int a * z pow 4 +
             real_of_int b * z pow 3 +
             real_of_int c * z pow 2 +
             real_of_int d * z +
             real_of_int e =
           real_of_int a *
             (z - r1) * (z - r2) * (z - r3) * (z - r4))
        ==>
        (rational (r1 + r2) /\ r1 + r2 <> r3 + r4
         ==>
         rational (r1 * r2))``;
