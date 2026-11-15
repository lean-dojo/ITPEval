(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_343. This file
  contains no proof.
*)

let statement =
  `(nproduct (0..5) (\k. 2 * k + 1)) MOD 10 = 5`;;
