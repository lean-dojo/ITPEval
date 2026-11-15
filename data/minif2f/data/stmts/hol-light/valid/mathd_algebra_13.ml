(* Statement-only formalization of miniF2F valid problem mathd_algebra_13. *)
let statement = `!a b:real.
    (!x.
       ~(x - &3 = &0) /\ ~(x - &5 = &0)
       ==> &4 * x / (x pow 2 - &8 * x + &15) =
           a / (x - &3) + b / (x - &5))
    ==> a = -- &6 /\ b = &10
`;;
