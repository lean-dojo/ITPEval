(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a4:
  the greatest uniform lower bound on a binary series selected by the parity
  of floors of positive integer multiples. This file contains no proof.
*)

let statement =
  `let even_floor =
     \x:real. \n:num.
       ?k:num.
         &(2 * k) <= &n * x /\
         &n * x < &(2 * k + 1) in
   let f =
     \x:real.
       sup {s:real |
              ?N:num.
                s =
                  sum (1..N)
                    (\n:num.
                       if even_floor x n
                       then &1 / ((&2:real) pow n)
                       else &0)} in
   (!x:real.
      &0 <= x /\ x < &1
      ==> &4 / &7 <= f x) /\
   (!l:real.
      (!x:real.
         &0 <= x /\ x < &1
         ==> l <= f x)
      ==> l <= &4 / &7)`;;
