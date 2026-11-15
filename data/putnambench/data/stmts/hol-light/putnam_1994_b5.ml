(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b5:
  existence, for every positive integer n, of a real alpha whose floor map
  has prescribed iterates at n squared and agrees there with the floor map
  for alpha raised to each relevant power. This file contains no proof.
*)

needs "Library/floor.ml";;
needs "Library/iter.ml";;

let statement =
  `let f =
     \alpha:real. \x:int.
       int_of_real (floor (alpha * real_of_int x)) in
   !n:num.
     0 < n
     ==> ?alpha:real.
           !k:num.
             1 <= k /\ k <= n
             ==> ITER k (f alpha) (&(n EXP 2):int) =
                 (&(n EXP 2):int) - &k /\
                 f (alpha pow k) (&(n EXP 2):int) =
                 (&(n EXP 2):int) - &k`;;
