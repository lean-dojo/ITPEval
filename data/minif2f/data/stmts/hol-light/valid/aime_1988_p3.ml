(*
  Statement-only formalization of miniF2F valid artifact aime_1988_p3:
  equality of nested base-2 and base-8 logarithms for a real greater than one
  implies
  that the square of its base-2 logarithm is 27. This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `!x:real.
     &1 < x /\
     ln (ln x / ln (&8)) / ln (&2) =
       ln (ln x / ln (&2)) / ln (&8)
     ==> (ln x / ln (&2)) pow 2 = &27`;;
