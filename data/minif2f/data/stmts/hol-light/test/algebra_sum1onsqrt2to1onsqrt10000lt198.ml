(*
  Statement-only formalization of miniF2F test problem algebra_sum1onsqrt2to1onsqrt10000lt198.
  This file contains no proof.
*)

let statement =
  `sum (2..10000) (\k:num. &1 / sqrt (&k)) < &198`;;
