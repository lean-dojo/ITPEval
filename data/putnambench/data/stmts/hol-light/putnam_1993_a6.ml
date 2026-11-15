(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a6:
  the positions of 2s in a self-referential infinite sequence of 2s and 3s
  are floor values of multiples of a real number. This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `!seq:num->num.
     (!n:num. seq n = 2 \/ seq n = 3) /\
     (!n:num.
        seq n = 2 <=>
        ?N:num.
          n = nsum {i:num | i < N} (\i. seq i + 1))
     ==>
     ?r:real.
       !n:num.
         seq n = 2 <=>
         ?m:num.
           &(n + 1) = &1 + floor (r * &m)`;;
