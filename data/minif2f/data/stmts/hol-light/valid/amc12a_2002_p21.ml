(* Statement-only formalization of miniF2F valid problem amc12a_2002_p21. *)
let statement = `!u:num->num.
    (u 0 = 4) /\
    (u 1 = 7) /\
    (!n. u (n + 2) = (u n + u (n + 1)) MOD 10)
    ==> (!n. nsum {k | k < n} u > 10000 ==> 1999 <= n)
`;;
