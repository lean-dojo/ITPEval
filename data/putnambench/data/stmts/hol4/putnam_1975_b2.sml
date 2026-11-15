(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b2:
  a sequence of open slabs in real three-space whose positive thicknesses
  have convergent partial sums cannot cover the whole space.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_1975_b2 =
  ``let dot3 =
      \u x : (real # real) # real.
        FST (FST u) * FST (FST x) +
        SND (FST u) * SND (FST x) +
        SND u * SND x
    in
    let norm3 =
      \u : (real # real) # real. sqrt (dot3 u u)
    in
    let slab =
      \normal : (real # real) # real.
      \offset thickness : real.
        {x : (real # real) # real |
           offset < dot3 normal x /\
           dot3 normal x < offset + thickness}
    in
      !normals : num -> (real # real) # real.
      !offsets thicknesses : num -> real.
        (!i : num. norm3 (normals i) = 1) /\
        (!i : num. 0 < thicknesses i) /\
        (?C : real.
           ((\n : num. SIGMA thicknesses (count n)) --> C) sequentially)
        ==>
        (UNIV : ((real # real) # real) set) <>
        BIGUNION
          (IMAGE
             (\i : num.
                slab (normals i) (offsets i) (thicknesses i))
             (UNIV : num set))``;
