(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b1:
  divisibility of an integer polynomial with nonnegative coefficients at a
  positive integer and at one more than its value. This file contains no proof.
*)

let statement =
  `let eval =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let nonnegative_coefficients =
     \p:int list.
       !i:num. i < LENGTH p ==> (&0:int) <= EL i p in
   let nonconstant =
     \p:int list.
       ?i:num. 0 < i /\ i < LENGTH p /\ (&0:int) < EL i p in
   !p:int list. !n:int.
     nonnegative_coefficients p /\
     nonconstant p /\
     (&0:int) < n
     ==>
     ((eval p n) divides (eval p (eval p n + &1)) <=> n = &1)`;;
