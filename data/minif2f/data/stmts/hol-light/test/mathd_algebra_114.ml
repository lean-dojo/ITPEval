(* Statement-only formalization of miniF2F test problem mathd_algebra_114. *)
let statement = `!a:real.
    a = &8
    ==> exp (&1 / &3 * ln (&16 * exp (&1 / &3 * ln (a pow 2)))) = &4
`;;
