(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a6:
  the impossibility of seven distinct real plane lines having at least six
  exact triple-intersection points and four exact double-intersection points.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val putnam_1973_a6 =
  ``!nint : num -> (num -> real # real) -> num.
      nint =
        (\n (lines : num -> real # real).
           CARD
             {p : real # real |
                ?!S : num set.
                  S SUBSET count 7 /\
                  CARD S = n /\
                  !i : num.
                    i IN S ==>
                    SND p =
                      FST (lines i) * FST p + SND (lines i)})
      ==>
      ~(?lines : num -> real # real.
          (!i j : num.
             i IN count 7 /\ j IN count 7 /\ i <> j
             ==>
             lines i <> lines j) /\
          6 <= nint 3 lines /\
          4 <= nint 2 lines)``;
