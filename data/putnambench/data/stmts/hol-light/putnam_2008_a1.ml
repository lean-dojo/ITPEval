(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a1:
  a cyclic-sum condition on a real-valued function of two real variables
  implies that the function is a difference of a real potential. This file
  contains no proof.
*)

let statement =
  `!f:real->real->real.
     (!x y z:real. f x y + f y z + f z x = &0)
     ==>
     ?g:real->real. !x y:real. f x y = g x - g y`;;
