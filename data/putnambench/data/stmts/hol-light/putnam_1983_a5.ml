(*
  Statement-only formalization of PutnamBench artifact putnam_1983_a5:
  existence of a positive real number whose positive integer powers have
  floors differing from their exponents by even integers. This file contains
  no proof.
*)

needs "Library/floor.ml";;

let statement =
  `let putnam_1983_a5_solution = T in
   ((?alpha:real.
       &0 < alpha /\
       !n:num.
         0 < n
         ==> (&2:int) divides
             (int_of_real (floor (alpha pow n)) - &n)) <=>
    putnam_1983_a5_solution)`;;
