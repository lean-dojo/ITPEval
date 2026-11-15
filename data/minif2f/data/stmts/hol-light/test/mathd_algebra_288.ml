(* Statement-only formalization of miniF2F test problem mathd_algebra_288. *)
let statement = `!x y n:real.
    (&0 <= n) /\
    (x < &0 /\ y < &0) /\
    (abs y = &6) /\
    (sqrt ((x - &8) pow 2 + (y - &3) pow 2) = &15) /\
    (sqrt (x pow 2 + y pow 2) = sqrt n)
==>
    (n = &52)
`;;
