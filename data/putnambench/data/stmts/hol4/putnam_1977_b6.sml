(*
  Statement-only formalization of PutnamBench artifact putnam_1977_b6:
  a finite subgroup whose elements x satisfy (x*a)^3 = 1 generates, through
  nonempty products of factors x*a, a set of cardinality at most 3h^2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory groupTheory;

val putnam_1977_b6 =
  ``!(g : 'a group) (H : 'a group) (a : 'a) (h : num) (P : 'a set).
      Group g /\
      Subgroup H g /\
      FINITE H.carrier /\
      a IN g.carrier /\
      h = CARD H.carrier /\
      (!x : 'a.
         x IN H.carrier
         ==>
         g.exp (g.op x a) 3 = g.id) /\
      P =
        {y : 'a |
           ?xs : 'a list.
             xs <> [] /\
             (!x : 'a. MEM x xs ==> x IN H.carrier) /\
             y =
               FOLDR
                 (\x acc. g.op (g.op x a) acc)
                 g.id
                 xs}
      ==>
      FINITE P /\ CARD P <= 3 * h ** 2``;
