(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b3:
  the exact supremum of the normalized k-th elementary symmetric sum over
  finite lists of positive real numbers of length at least k.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1975_b3 =
  ``let esymm =
      \k : num.
      \a : real list.
        SIGMA
          (\s : num set.
             REAL_PROD_IMAGE (\i : num. EL i a) s)
          {s : num set |
             s SUBSET count (LENGTH a) /\ CARD s = k}
    in
    let admissible =
      \k : num.
      \a : real list.
        k <= LENGTH a /\
        !i : num. i < LENGTH a ==> 0 < EL i a
    in
    let solution =
      \k : num. 1 / &(FACT k)
    in
      !k : num.
        0 < k
        ==>
        (!a : real list.
           admissible k a
           ==>
           esymm k a / (esymm 1 a) pow k <= solution k) /\
        !M : real.
          M < solution k
          ==>
          ?a : real list.
            admissible k a /\
            M < esymm k a / (esymm 1 a) pow k``;
