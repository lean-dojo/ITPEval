(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b3:
  irrationality of every real alpha satisfying cos(pi * alpha) = 1/3.
  This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   !alpha:real.
     cos (pi * alpha) = &1 / &3
     ==> ~is_rational alpha`;;
