(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a5:
  a group contained in real three-space in which each pair's cross product
  equals either its group product or zero must have all pairwise cross products
  equal to zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory groupTheory;

val putnam_2010_a5 =
  ``let zero3 = ((0, 0), 0) : (real # real) # real
    in
    let cross3 =
      \a b : (real # real) # real.
        ((SND (FST a) * SND b - SND a * SND (FST b),
          SND a * FST (FST b) - FST (FST a) * SND b),
         FST (FST a) * SND (FST b) -
           SND (FST a) * FST (FST b))
    in
      !(g : ((real # real) # real) group).
        Group g /\
        (!a b : (real # real) # real.
           a IN g.carrier /\ b IN g.carrier
           ==>
           cross3 a b = g.op a b \/ cross3 a b = zero3)
        ==>
        !a b : (real # real) # real.
          a IN g.carrier /\ b IN g.carrier
          ==>
          cross3 a b = zero3``;
