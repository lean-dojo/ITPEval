(*
  Statement-only formalization of miniF2F valid problem aime_1997_p11: if a real number is the
  ratio of the cosine and sine sums for the angles from 1 through 44 degrees, then the floor of
  100 times that number is 241. This file contains no proof.
*)

needs "Library/floor.ml";;

let statement = `!x:real.
    x =
      (sum (1..44) (\n:num. cos (&n * pi / &180))) /
      (sum (1..44) (\n:num. sin (&n * pi / &180)))
    ==> floor (&100 * x) = &241
`;;
