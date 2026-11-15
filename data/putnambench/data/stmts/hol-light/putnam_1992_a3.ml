(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a3:
  classification of the positive integer solutions to
  (x^2 + y^2)^m = (xy)^n when n is coprime to m. This file contains no proof.
*)

let statement =
  `!m n x y:num.
     0 < m
     ==>
     ((?r:num.
         x = 2 EXP r /\
         y = 2 EXP r /\
         n = 2 * r + 1 /\
         m = 2 * r) <=>
      0 < n /\
      0 < x /\
      0 < y /\
      coprime(n,m) /\
      (x EXP 2 + y EXP 2) EXP m = (x * y) EXP n)`;;
