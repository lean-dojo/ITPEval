(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b1:
  the cubic plane curve x^3 + 3xy + y^3 = 1 contains a unique three-point
  equilateral triangle, whose area is 3 * sqrt 3 / 2. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_2006_b1 =
  ``let cubic_curve =
      {P : real # real |
         FST P pow 3 + 3 * FST P * SND P + SND P pow 3 = 1}
    in
    let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let equilateral =
      \S : (real # real) set.
        FINITE S /\
        CARD S = 3 /\
        ?d : real.
          !P Q : real # real.
            P IN S /\ Q IN S /\ P <> Q ==> dist P Q = d
    in
    let in_convex_hull =
      \S : (real # real) set.
      \X : real # real.
        ?w : (real # real) -> real.
          (!P : real # real. P IN S ==> 0 <= w P) /\
          SIGMA w S = 1 /\
          X =
            (SIGMA (\P : real # real. w P * FST P) S,
             SIGMA (\P : real # real. w P * SND P) S)
    in
    let area =
      measure (prod_measure_space lebesgue lebesgue)
    in
      (?!S : (real # real) set.
         S SUBSET cubic_curve /\ equilateral S) /\
      (?S : (real # real) set.
         S SUBSET cubic_curve /\
         equilateral S /\
         area (in_convex_hull S) = Normal (3 * sqrt 3 / 2))``;
