(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a4:
  the least number of paper-punch centers needed so every point in the real
  Euclidean plane is at irrational distance from some center is three. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_of_ratTheory
     transcTheory;

val putnam_1990_a4 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let covers =
      \S : (real # real) set.
        !Q : real # real.
          ?P : real # real.
            P IN S /\ dist P Q NOTIN q_set
    in
      (LEAST n : num.
         ?S : (real # real) set.
           FINITE S /\ CARD S = n /\ covers S) =
      3``;
