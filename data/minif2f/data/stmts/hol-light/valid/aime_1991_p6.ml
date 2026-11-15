(*
  Statement-only formalization of miniF2F valid problem aime_1991_p6. This file contains no
  proof.
*)

needs "Library/floor.ml";;

let statement = `!r:real.
    sum (19..91) (\k:num. floor (r + &k / &100)) = &546
    ==> floor (&100 * r) = &743
`;;
