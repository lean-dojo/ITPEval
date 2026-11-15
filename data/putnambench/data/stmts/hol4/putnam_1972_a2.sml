(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a2:
  commutativity of magmas satisfying two involutive identities, together with
  the existence of a nonassociative example. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val putnam_1972_a2 =
  ``(!f : 'a -> 'a -> 'a.
        (!x y : 'a.
           f x (f x y) = y /\
           f (f y x) x = y)
        ==>
        !x y : 'a. f x y = f y x) /\
    (?g : int -> int -> int.
       (!x y : int.
          g x (g x y) = y /\
          g (g y x) x = y) /\
       ~(!x y z : int.
           g x (g y z) = g (g x y) z))``;
