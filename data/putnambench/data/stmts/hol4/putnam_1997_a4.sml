(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a4:
  a function on an arbitrary group whose triple product is constant on triples
  with product equal to the identity can be left-translated into a group
  homomorphism. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory groupTheory;

val putnam_1997_a4 =
  ``!(g : 'a group) (phi : 'a -> 'a).
      Group g /\
      g.carrier = UNIV /\
      (!g1 g2 g3 h1 h2 h3 : 'a.
         (g.op (g.op g1 g2) g3 = g.id /\
          g.op (g.op h1 h2) h3 = g.id)
         ==>
         g.op (g.op (phi g1) (phi g2)) (phi g3) =
         g.op (g.op (phi h1) (phi h2)) (phi h3))
      ==>
      ?a : 'a.
        !x y : 'a.
          g.op a (phi (g.op x y)) =
          g.op (g.op a (phi x)) (g.op a (phi y))``;
