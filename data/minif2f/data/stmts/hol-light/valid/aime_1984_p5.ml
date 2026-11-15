(* Statement-only formalization of miniF2F valid problem aime_1984_p5. *)
let statement = `!a b:real.
    &0 < a /\ &0 < b /\
    (ln a / ln (&8) + ln (b pow 2) / ln (&4) = &5) /\
    (ln b / ln (&8) + ln (a pow 2) / ln (&4) = &7)
    ==> a * b = &512
`;;
