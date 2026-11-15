(* Statement-only formalization of miniF2F valid problem induction_sum2kp1npqsqm1. *)
let statement =
  `!n:num.
     nsum {k | k < n} (\k. 2 * k + 3) = (n + 1) EXP 2 - 1`;;
