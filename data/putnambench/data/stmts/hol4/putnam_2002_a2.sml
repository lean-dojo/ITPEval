(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a2:
  among any five points on the unit sphere in real three-space, four lie in
  a common closed hemisphere. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val putnam_2002_a2 =
  ``let sphere3 =
      \P : (real # real) # real.
        FST (FST P) * FST (FST P) +
        SND (FST P) * SND (FST P) +
        SND P * SND P = 1
    in
    let dot3 =
      \P V : (real # real) # real.
        FST (FST P) * FST (FST V) +
        SND (FST P) * SND (FST V) +
        SND P * SND V
    in
      !S : ((real # real) # real) set.
        FINITE S /\
        S SUBSET {P : (real # real) # real | sphere3 P} /\
        CARD S = 5
        ==>
        ?V : (real # real) # real.
          V <> ((0, 0), 0) /\
          4 <= CARD (S INTER {P : (real # real) # real | 0 <= dot3 P V})``;
