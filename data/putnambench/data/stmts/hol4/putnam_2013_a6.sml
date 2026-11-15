(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a6:
  strict positivity of a finite weighted double sum over integer lattice
  points for the specified compactly supported weight. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory;

val putnam_2013_a6 =
  ``!w : int -> int -> int.
      !A : (int # int) set -> int.
        w (-2) (-2) = -1 /\
        w 2 (-2) = -1 /\
        w (-2) 2 = -1 /\
        w 2 2 = -1 /\
        w (-1) (-2) = -2 /\
        w 1 (-2) = -2 /\
        w (-2) (-1) = -2 /\
        w 2 (-1) = -2 /\
        w (-2) 1 = -2 /\
        w 2 1 = -2 /\
        w (-1) 2 = -2 /\
        w 1 2 = -2 /\
        w 0 (-2) = 2 /\
        w (-2) 0 = 2 /\
        w 2 0 = 2 /\
        w 0 2 = 2 /\
        w (-1) (-1) = 4 /\
        w 1 (-1) = 4 /\
        w (-1) 1 = 4 /\
        w 1 1 = 4 /\
        w 0 (-1) = -4 /\
        w (-1) 0 = -4 /\
        w 1 0 = -4 /\
        w 0 1 = -4 /\
        w 0 0 = 12 /\
        (!a b : int.
           2 < ABS a \/ 2 < ABS b
           ==>
           w a b = 0) /\
        (!S : (int # int) set.
           FINITE S
           ==>
           A S =
             SIGMA
               (\s : int # int.
                  SIGMA
                    (\t : int # int.
                       w (FST s - FST t) (SND s - SND t))
                    S)
               S)
        ==>
        !S : (int # int) set.
          FINITE S /\ S <> {}
          ==>
          0 < A S``;
