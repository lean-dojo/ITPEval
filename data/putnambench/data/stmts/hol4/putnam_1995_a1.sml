(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a1:
  a multiplicatively closed set of real numbers partitioned into two disjoint
  subsets that are each closed under triple products has at least one subset
  closed under binary products. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;

val putnam_1995_a1 =
  ``!S T U : real set.
      (!a b : real.
         a IN S /\ b IN S
         ==>
         a * b IN S) /\
      T SUBSET S /\
      U SUBSET S /\
      T UNION U = S /\
      DISJOINT T U /\
      (!a b c : real.
         a IN T /\ b IN T /\ c IN T
         ==>
         a * b * c IN T) /\
      (!a b c : real.
         a IN U /\ b IN U /\ c IN U
         ==>
         a * b * c IN U)
      ==>
      (!a b : real.
         a IN T /\ b IN T
         ==>
         a * b IN T) \/
      (!a b : real.
         a IN U /\ b IN U
         ==>
         a * b IN U)``;
