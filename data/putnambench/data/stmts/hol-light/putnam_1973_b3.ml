(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b3:
  primality of x^2 - x + p on the natural range below p implies a unique
  integer triple with the prescribed discriminant and reduction inequalities.
  This file contains no proof.
*)

let statement =
  `!p:num.
     p > 1 /\
     (!x:num. x < p ==> prime (x EXP 2 - x + p))
     ==> ?!(a,b,c):int#int#int.
           b pow 2 - (&4:int) * a * c = &1 - &4 * &p /\
           (&0:int) < a /\
           a <= c /\
           --a <= b /\
           b < a`;;
