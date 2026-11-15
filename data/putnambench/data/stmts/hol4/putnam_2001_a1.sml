(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_a1:
  a binary operation satisfying (a op b) op a = b also satisfies
  a op (b op a) = b on an arbitrary carrier. This file contains no proof.
*)

open HolKernel Parse boolLib;

val putnam_2001_a1 =
  ``!(op : 'a -> 'a -> 'a).
      (!a b : 'a. op (op a b) a = b)
      ==>
      !a b : 'a. op a (op b a) = b``;
