(* Statement-only formalization of miniF2F test problem mathd_numbertheory_618. *)
let statement = `!n:num p:num->num.
    0 < n /\
    (!x. p x = x EXP 2 - x + 41) /\
    (1 < gcd (p n,p (n + 1)))
==>
    (41 <= n)
`;;
