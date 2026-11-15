(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a6:
  the minimum degree, namely 25, of a monic integer polynomial whose value
  at every integer is divisible by 1000000. This file contains no proof.
*)

let statement =
  `let eval =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let admissible =
     \p:int list.
       ~(p = []) /\
       LAST p = &1 /\
       (!x:int. (&1000000:int) divides eval p x) in
   (?p:int list. admissible p /\ LENGTH p = 25 + 1) /\
   (!d:num.
      d < 25
      ==> ~(?p:int list. admissible p /\ LENGTH p = d + 1))`;;
