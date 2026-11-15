(*
  Statement-only formalization of miniF2F valid problem aime_1994_p4. This file contains no
  proof.
*)

needs "Library/floor.ml";;

let statement = `!n:num.
    0 < n /\
    sum (1..n) (\k:num. floor (ln (&k) / ln (&2))) = &1994
    ==> n = 312
`;;
