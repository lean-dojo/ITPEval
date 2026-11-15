(*
  Statement-only formalization of miniF2F test problem
  algebra_ineq_nto1onlt2m1on. This file contains no proof.
*)

let statement =
  `!n:num. exp ((&1 / &n) * ln (&n)) <= &2 - &1 / &n`;;
