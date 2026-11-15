(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b1:
  every composite positive integer, presented as a product of two integers at
  least 2, is expressible as xy + xz + yz + 1 for positive integers x, y, z.
  This file contains no proof.
*)

let statement =
  `!a:int.
     a >= &2
     ==> !b:int.
           b >= &2
           ==> ?x y z:int.
                 x > &0 /\
                 y > &0 /\
                 z > &0 /\
                 a * b = x * y + x * z + y * z + &1`;;
