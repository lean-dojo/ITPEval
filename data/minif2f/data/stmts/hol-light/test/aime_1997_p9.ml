(*
  Statement-only formalization of miniF2F test problem aime_1997_p9. This file contains no
  proof.
*)

needs "Library/floor.ml";;

let statement = `!a:real.
    &0 < a /\
    (&1 / a) - floor (&1 / a) = a pow 2 - floor (a pow 2) /\
    &2 < a pow 2 /\
    a pow 2 < &3
    ==> a pow 12 - &144 * (&1 / a) = &233
`;;
