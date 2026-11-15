(*
  Statement-only formalization of miniF2F test problem
  algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1. This file contains no proof.
*)

let statement =
  `!x:real.
     abs (x - &1) + abs x + abs (x + &1) = x + &2
     ==> &0 <= x /\ x <= &1`;;
