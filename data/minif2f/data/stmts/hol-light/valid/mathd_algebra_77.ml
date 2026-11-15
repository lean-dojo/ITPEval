(* Statement-only formalization of miniF2F valid problem mathd_algebra_77. *)
let statement = `!a b:real f:real->real.
    (~(a = &0) /\ ~(b = &0)) /\
    ~(a = b) /\
    (!x. f x = x pow 2 + a * x + b) /\
    (f a = &0) /\
    (f b = &0)
    ==> a = &1 /\ b = -- &2
`;;
