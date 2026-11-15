(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a2:
  a commutative associative binary operation with a solution to x op z = y
  for every x and y satisfies cancellation at any fixed right factor.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val putnam_2012_a2 =
  ``!(op : 'a -> 'a -> 'a). !a b c : 'a.
      (!x y : 'a. op x y = op y x) /\
      (!x y z : 'a. op x (op y z) = op (op x y) z) /\
      (!x y : 'a. ?z : 'a. op x z = y) /\
      op a c = op b c
      ==>
      a = b``;
