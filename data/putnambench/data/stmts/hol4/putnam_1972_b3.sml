(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b3:
  group relations forcing an element whose positive odd power is the identity
  to be the identity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory groupTheory;

val putnam_1972_b3 =
  ``!(g : 'a group) (A B : 'a).
      Group g /\
      A IN g.carrier /\
      B IN g.carrier /\
      g.op (g.op A B) A =
        g.op (g.op B (g.exp A 2)) B /\
      g.exp A 3 = g.id /\
      (?n : num.
         0 < n /\
         g.exp B (2 * n - 1) = g.id)
      ==>
      B = g.id``;
