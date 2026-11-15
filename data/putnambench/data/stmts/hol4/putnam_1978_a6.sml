(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a6:
  fewer than twice n to the three-halves unordered pairs among n distinct
  points in the real plane are one unit apart. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;

val putnam_1978_a6 =
  ``!S : (real # real) set. !n : num.
      let dist =
        \P Q : real # real.
          sqrt
            ((FST P - FST Q) pow 2 +
             (SND P - SND Q) pow 2)
      in
        n = CARD S /\ 0 < n /\ FINITE S
        ==>
        (&(CARD
             {pair : (real # real) set |
                ?P Q : real # real.
                  P IN S /\ Q IN S /\
                  pair = {P; Q} /\
                  dist P Q = 1}) : real) <
          2 * (&n : real) powr ((3 : real) / 2)``;
