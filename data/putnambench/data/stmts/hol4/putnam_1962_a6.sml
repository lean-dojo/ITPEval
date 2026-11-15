(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a6:
  characterization of an addition- and multiplication-closed set of rational
  numbers satisfying exact sign trichotomy as the positive rationals. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory ratTheory;

val putnam_1962_a6 =
  ``!(S : rat set).
      (!a b : rat.
         a IN S /\ b IN S
         ==>
         a + b IN S) /\
      (!a b : rat.
         a IN S /\ b IN S
         ==>
         a * b IN S) /\
      (!r : rat.
         (r IN S \/ ~r IN S \/ r = 0q) /\
         ~(r IN S /\ ~r IN S) /\
         ~(r IN S /\ r = 0q) /\
         ~(~r IN S /\ r = 0q))
      ==>
      S = {r : rat | 0q < r}``;
