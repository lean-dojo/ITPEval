(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b2:
  classification of the nonzero real pairs satisfying a specified system of
  two rational polynomial equations. This file contains no proof.
*)

let statement =
  `!x y:real.
     ~(x = &0) /\ ~(y = &0)
     ==>
     ((&1 / x + &1 / (&2 * y) =
         (x pow 2 + &3 * y pow 2) * (&3 * x pow 2 + y pow 2) /\
       &1 / x - &1 / (&2 * y) =
         &2 * (y pow 4 - x pow 4))
      <=>
      (?r:real.
         &0 < r /\
         r pow 5 = &3 /\
         x = (r + &1) / &2 /\
         y = (r - &1) / &2))`;;
