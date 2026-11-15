(* Statement-only formalization of miniF2F test problem mathd_algebra_487. *)
let statement = `!a b c d:real.
    (b = a pow 2) /\
    (a + b = &1) /\
    (d = c pow 2) /\
    (c + d = &1) /\
    ~(a = c)
==>
    (sqrt ((a - c) pow 2 + (b - d) pow 2) = sqrt (&10))
`;;
