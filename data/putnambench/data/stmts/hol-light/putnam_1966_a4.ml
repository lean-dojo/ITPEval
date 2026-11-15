(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a4:
  the closed form for the increasing sequence of positive integers that
  omits perfect squares. This file contains no proof.
*)

let statement =
  `let nearest_integer =
     \x:real.
       @z:int.
         real_of_int z - &1 / &2 <= x /\
         x < real_of_int z + &1 / &2 in
   !a:num->int.
     a 1 = &2 /\
     (!n:num.
        1 <= n
        ==> a (n + 1) =
            (if ?m:int. m pow 2 = a n + &1
             then a n + &2
             else a n + &1))
     ==> !n:num.
           1 <= n
           ==> a n = &n + nearest_integer (sqrt (&n))`;;
