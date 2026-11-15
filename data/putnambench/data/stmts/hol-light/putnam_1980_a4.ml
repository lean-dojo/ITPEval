(*
  Statement-only formalization of PutnamBench artifact putnam_1980_a4:
  bounded nonzero integer combinations of 1, sqrt 2, and sqrt 3 have both
  an explicit close approximation to zero and a uniform lower bound.
  This file contains no proof.
*)

let statement =
  `let abcvals =
     \a b c:int.
       ~(a = &0 /\ b = &0 /\ c = &0) /\
       abs a < &1000000 /\
       abs b < &1000000 /\
       abs c < &1000000 in
   (?a b c:int.
      abcvals a b c /\
      abs (real_of_int a +
           real_of_int b * sqrt (&2) +
           real_of_int c * sqrt (&3))
      < &1 / (&10 pow 11)) /\
   (!a b c:int.
      abcvals a b c
      ==> abs (real_of_int a +
               real_of_int b * sqrt (&2) +
               real_of_int c * sqrt (&3))
          > &1 / (&10 pow 21))`;;
