(* Statement-only formalization of miniF2F valid problem mathd_numbertheory_257. *)
let statement = `!x:num.
    (1 <= x /\ x <= 100) /\
    (77 divides (nsum (0..100) (\k. k) - x))
    ==> (x = 45)
`;;
