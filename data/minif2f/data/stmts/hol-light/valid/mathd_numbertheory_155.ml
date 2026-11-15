(* Statement-only formalization of miniF2F valid problem mathd_numbertheory_155. *)
let statement =
  `CARD {x:num | 100 <= x /\ x <= 999 /\ x MOD 19 = 7} = 48`;;
