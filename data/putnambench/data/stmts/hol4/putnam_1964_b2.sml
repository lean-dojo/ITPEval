(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b2:
  a maximal pairwise-intersecting family of subsets of a nonempty finite set
  contains exactly half of all subsets. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1964_b2 =
  ``!(P : ('a set) set).
      FINITE (UNIV : 'a set) /\
      0 < CARD (UNIV : 'a set) /\
      FINITE P /\
      (!T U : 'a set.
         T IN P /\ U IN P
         ==>
         T INTER U <> {}) /\
      ~(?T : 'a set.
          T NOTIN P /\
          (!U : 'a set.
             U IN P
             ==>
             T INTER U <> {}))
      ==>
      CARD P = 2 EXP (CARD (UNIV : 'a set) - 1)``;
