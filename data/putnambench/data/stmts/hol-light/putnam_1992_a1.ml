(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a1:
  characterization of the unique integer-valued function satisfying an
  involution identity, a shifted functional identity, and f(0) = 1. This file
  contains no proof.
*)

let statement =
  `!f:int->int.
     (f = (\n:int. &1 - n)) <=>
     ((!n:int. f (f n) = n) /\
      (!n:int. f (f (n + &2) + &2) = n) /\
      f (&0) = &1)`;;
