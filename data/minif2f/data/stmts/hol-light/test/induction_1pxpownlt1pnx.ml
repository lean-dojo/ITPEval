(*
  Statement-only formalization of miniF2F test problem
  induction_1pxpownlt1pnx. This file contains no proof.
*)

let statement =
  `!x:real n:num.
     0 < n /\ --(&1) < x
     ==> &1 + &n * x <= (&1 + x) pow n`;;
