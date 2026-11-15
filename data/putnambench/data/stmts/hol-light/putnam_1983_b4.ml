(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b4:
  every positive-integer sequence obtained by repeatedly adding the floor of
  the square root of its current term eventually contains a perfect square.
  This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `!a:num->num.
     0 < a 0 /\
     (!n:num.
        a (n + 1) =
        a n + num_of_int (int_of_real (floor (sqrt (&(a n))))))
     ==> ?i s:num. a i = s EXP 2`;;
