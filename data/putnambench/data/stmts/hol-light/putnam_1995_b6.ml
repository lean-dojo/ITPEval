(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b6:
  the positive natural numbers cannot be partitioned into three pairwise
  disjoint sets of floors of positive integer multiples of positive reals.
  This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `let S =
     \alpha:real.
       {x:num | ?n:num. 1 <= n /\ &x = floor (&n * alpha)} in
   ~(?alpha beta gamma:real.
       &0 < alpha /\
       &0 < beta /\
       &0 < gamma /\
       S alpha INTER S beta = {} /\
       S beta INTER S gamma = {} /\
       S alpha INTER S gamma = {} /\
       {x:num | 1 <= x} = S alpha UNION S beta UNION S gamma)`;;
