(*
  Statement-only formalization of miniF2F test problem imo_1969_p2. This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `!m n:real.
   !k:num.
   !a:num->real.
   !y:real->real.
     0 < k /\
     (!x:real.
        y x =
        sum (0..(k - 1))
          (\i. cos (a i + x) / (&2 pow i))) /\
     y m = &0 /\
     y n = &0
     ==> ?t:int. m - n = real_of_int t * pi`;;
