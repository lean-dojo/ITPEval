(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b2:
  existence of a real-indexed family of subsets of the natural numbers that
  is strictly increasing under proper inclusion. This file contains no proof.
*)

let statement =
  `?f:real->num->bool.
     !a b:real. a < b ==> f a PSUBSET f b`;;
