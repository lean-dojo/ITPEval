(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b1:
  two distinct affine lines in the real plane intersect exactly when the
  prescribed nonzero dilation condition holds from every point off both
  lines. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory;

val putnam_2017_b1 =
  ``let add2 =
      \P Q : real # real.
        (FST P + FST Q, SND P + SND Q)
    in
    let sub2 =
      \P Q : real # real.
        (FST P - FST Q, SND P - SND Q)
    in
    let smul2 =
      \c : real.
      \P : real # real.
        (c * FST P, c * SND P)
    in
      !lines : (real # real) set set.
      !L1 L2 : (real # real) set.
        lines =
          {L : (real # real) set |
             ?v w : real # real.
               w <> (0, 0) /\
               L =
                 {p : real # real |
                    ?t : real. p = add2 v (smul2 t w)}} /\
        L1 IN lines /\
        L2 IN lines /\
        L1 <> L2
        ==>
        ((L1 INTER L2 <> EMPTY) <=>
         !lambda : real.
           lambda <> 0
           ==>
           !P : real # real.
             P NOTIN L1 /\ P NOTIN L2
             ==>
             ?A1 A2 : real # real.
               A1 IN L1 /\
               A2 IN L2 /\
               sub2 A2 P = smul2 lambda (sub2 A1 P))``;
