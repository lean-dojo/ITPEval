(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b4:
  emptiness of the intersection of all positive iterate images of the
  rational map x |-> x - 1/x on the rationals excluding -1, 0, and 1.
  This file contains no proof.
*)

needs "Library/iter.ml";;

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   let S =
     {x:real |
        is_rational x /\
        ~(x = -- &1) /\
        ~(x = &0) /\
        ~(x = &1)} in
   let f =
     \x:real. x - &1 / x in
   ~(?x:real.
       !n:num.
         1 <= n
         ==> x IN IMAGE (ITER n f) S)`;;
