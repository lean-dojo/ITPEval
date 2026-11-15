(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b5:
  the number of 2 by 2 matrices over a prime residue field with trace one
  and determinant zero is p squared plus p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory ringTheory;

val putnam_1968_b5 =
  ``!p : num.
      prime p
      ==>
      CARD
        {M : (num # num) # (num # num) |
           FST (FST M) IN (ZN p).carrier /\
           SND (FST M) IN (ZN p).carrier /\
           FST (SND M) IN (ZN p).carrier /\
           SND (SND M) IN (ZN p).carrier /\
           (ZN p).sum.op (FST (FST M)) (SND (SND M)) =
             (ZN p).prod.id /\
           (ZN p).sum.op
             ((ZN p).prod.op (FST (FST M)) (SND (SND M)))
             ((ZN p).sum.inv
                ((ZN p).prod.op (SND (FST M)) (FST (SND M)))) =
             (ZN p).sum.id} =
      p EXP 2 + p``;
