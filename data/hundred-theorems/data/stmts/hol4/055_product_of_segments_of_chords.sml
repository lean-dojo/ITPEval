(*
  Statement-only formalization of Hundred Theorems artifact 055,
  "Product of Segments of Chords": in the real coordinate plane, two
  chords of a circle meeting at a common point have equal products of
  their segment lengths. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val product_of_segments_of_chords =
  ``!centre radius q r s t b.
      (?u.
         0 <= u /\ u <= 1 /\
         FST b = u * FST q + (1 - u) * FST r /\
         SND b = u * SND q + (1 - u) * SND r) /\
      (?v.
         0 <= v /\ v <= 1 /\
         FST b = v * FST s + (1 - v) * FST t /\
         SND b = v * SND s + (1 - v) * SND t) /\
      sqrt ((FST q - FST centre) pow 2 +
            (SND q - SND centre) pow 2) = radius /\
      sqrt ((FST r - FST centre) pow 2 +
            (SND r - SND centre) pow 2) = radius /\
      sqrt ((FST s - FST centre) pow 2 +
            (SND s - SND centre) pow 2) = radius /\
      sqrt ((FST t - FST centre) pow 2 +
            (SND t - SND centre) pow 2) = radius
      ==>
      sqrt ((FST q - FST b) pow 2 + (SND q - SND b) pow 2) *
        sqrt ((FST b - FST r) pow 2 + (SND b - SND r) pow 2) =
      sqrt ((FST s - FST b) pow 2 + (SND s - SND b) pow 2) *
        sqrt ((FST b - FST t) pow 2 + (SND b - SND t) pow 2)``;
