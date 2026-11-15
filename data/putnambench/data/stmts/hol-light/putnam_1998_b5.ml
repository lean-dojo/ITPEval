(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b5:
  the thousandth decimal digit of the square root of the 1998-digit repunit.
  This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `let N = nsum (0..1997) (\i:num. 10 EXP i) in
   num_of_int
     (int_of_real
       (floor (((&10:real) pow 1000) * sqrt (&N)))) MOD 10 = 1`;;
