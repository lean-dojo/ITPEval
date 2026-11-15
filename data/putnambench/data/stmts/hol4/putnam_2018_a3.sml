(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a3:
  the greatest possible sum of cosines of three times ten real angles,
  subject to the sum of their cosines being zero, is 480/49. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_2018_a3 =
  ``let solution = (480 / 49 : real)
    in
    let feasible =
      \x : num -> real.
        SIGMA (\i : num. cos (x i)) (count 10) = 0
    in
    let objective =
      \x : num -> real.
        SIGMA (\i : num. cos (3 * x i)) (count 10)
    in
      (!x : num -> real. feasible x ==> objective x <= solution) /\
      (?x : num -> real. feasible x /\ objective x = solution)``;
