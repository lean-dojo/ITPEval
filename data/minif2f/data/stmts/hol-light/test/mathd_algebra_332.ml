(* Statement-only formalization of miniF2F test problem mathd_algebra_332. *)
let statement = `!x y:real.
    ((x + y) / &2 = &7) /\
    (sqrt (x * y) = sqrt (&19))
==>
    x pow 2 + y pow 2 = &158
`;;
