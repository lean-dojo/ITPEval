(* Statement-only formalization of miniF2F valid problem induction_sum_odd. *)
let statement =
  `!n:num. nsum {k | k < n} (\k. 2 * k + 1) = n EXP 2`;;
