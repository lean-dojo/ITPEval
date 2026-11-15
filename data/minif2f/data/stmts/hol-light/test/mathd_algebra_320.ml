(* Statement-only formalization of miniF2F test problem mathd_algebra_320. *)
let statement = `!x:real a b c:num.
    (&0 <= x /\ 0 < a /\ 0 < b /\ 0 < c) /\
    (&2 * x pow 2 = &4 * x + &9) /\
    (x = (&a + sqrt (&b)) / &c) /\
    (c = 2)
==>
    a + b + c = 26
`;;
