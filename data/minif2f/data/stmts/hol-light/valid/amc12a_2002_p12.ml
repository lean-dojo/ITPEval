(* Statement-only formalization of miniF2F valid problem amc12a_2002_p12. *)
let statement = `!f:real->real k:real a b:num.
    (!x. f x = x pow 2 - &63 * x + k) /\
    f (&a) = &0 /\ f (&b) = &0 /\
    ~(a = b) /\ prime a /\ prime b
    ==> k = &122
`;;
