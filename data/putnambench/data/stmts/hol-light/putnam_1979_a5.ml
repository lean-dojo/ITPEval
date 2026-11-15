(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a5:
  two distinct real roots of the given cubic have floor-multiple sequences
  sharing arbitrarily large integers. This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `let S = \x:real. \n:num. int_of_real (floor (&n * x)) in
   let P =
     \x:real. x pow 3 - &10 * x pow 2 + &29 * x - &25 = &0 in
   ?alpha beta:real.
     ~(alpha = beta) /\
     P alpha /\
     P beta /\
     !n:num.
       ?m:int.
         &n < m /\
         ?c d:num.
           S alpha c = m /\
           S beta d = m`;;
