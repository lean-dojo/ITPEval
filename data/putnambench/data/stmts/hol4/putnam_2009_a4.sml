(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a4:
  whether a set of rational numbers closed under unit translations and the
  specified reciprocal transformation must contain every rational, with
  answer false. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory ratTheory;

val putnam_2009_a4 =
  ``((!S : rat set.
        0q IN S
        ==>
        (!x : rat.
           x IN S
           ==>
           x + 1q IN S /\ x - 1q IN S)
        ==>
        (!x : rat.
           x IN S /\ x <> 0q /\ x <> 1q
           ==>
           1q / (x * (x - 1q)) IN S)
        ==>
        !r : rat. r IN S)
     <=>
     F)``;
