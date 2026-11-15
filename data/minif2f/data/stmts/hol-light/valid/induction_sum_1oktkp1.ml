(* Statement-only formalization of miniF2F valid problem induction_sum_1oktkp1. *)
let statement =
  `!n:num.
     sum {k | k < n} (\k. &1 / &((k + 1) * (k + 2))) =
     &n / &(n + 1)`;;
