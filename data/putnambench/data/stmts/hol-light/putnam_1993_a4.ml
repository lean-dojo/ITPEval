(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a4:
  equal subset sums for 19 positive integers bounded by 93 and 93 positive
  integers bounded by 19, with the first subset nonempty. This file contains
  no proof.
*)

let statement =
  `!x y:num->num.
     ((!i:num. i IN 0..18 ==> 1 <= x i /\ x i <= 93) /\
      (!j:num. j IN 0..92 ==> 1 <= y j /\ y j <= 19))
     ==>
     ?is js:num->bool.
       is SUBSET (0..18) /\
       js SUBSET (0..92) /\
       ~(is = {}) /\
       nsum is x = nsum js y`;;
