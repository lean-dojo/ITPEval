(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a1:
  among any nine lattice points in real three-space, the open segment joining
  some two distinct points contains a lattice point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory realTheory intrealTheory;

val putnam_1971_a1 =
  ``!S : ((int # int) # int) -> bool.
      S HAS_SIZE 9
      ==>
      ?x y z : int.
      ?P Q : (int # int) # int.
      ?t : real.
        P IN S /\
        Q IN S /\
        P <> Q /\
        0 < t /\
        t < 1 /\
        real_of_int x =
          t * real_of_int (FST (FST P)) +
          (1 - t) * real_of_int (FST (FST Q)) /\
        real_of_int y =
          t * real_of_int (SND (FST P)) +
          (1 - t) * real_of_int (SND (FST Q)) /\
        real_of_int z =
          t * real_of_int (SND P) +
          (1 - t) * real_of_int (SND Q)``;
