(* Statement-only formalization of miniF2F valid problem mathd_algebra_421. *)
let statement = `!a b c d:real.
    (b = a pow 2 + &4 * a + &6) /\
    (b = &1 / &2 * a pow 2 + a + &6) /\
    (d = c pow 2 + &4 * c + &6) /\
    (d = &1 / &2 * c pow 2 + c + &6) /\
    (a < c)
    ==> (c - a = &6)
`;;
