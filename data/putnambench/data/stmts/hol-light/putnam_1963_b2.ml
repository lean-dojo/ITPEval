(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b2:
  density in the positive reals of products 2^m * 3^n with integer
  exponents m and n. This file contains no proof.
*)

let statement =
  `!x:real.
     &0 < x
     ==> !e. &0 < e
             ==> ?m n:int.
                   abs(((&2):real) zpow m *
                       ((&3):real) zpow n - x) < e`;;
