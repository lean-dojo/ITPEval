(* Statement-only formalization of miniF2F valid problem mathd_algebra_96. *)
let statement = `!x y z a:real.
    (&0 < x /\ &0 < y /\ &0 < z) /\
    (ln x - ln y = a) /\
    (ln y - ln z = &15) /\
    (ln z - ln x = -- &7)
    ==> a = -- &8
`;;
