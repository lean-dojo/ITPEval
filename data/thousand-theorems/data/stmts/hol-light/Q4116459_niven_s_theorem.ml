(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4116459,
  "Niven's theorem": if a real angle is a rational multiple of pi and has
  rational cosine, then that cosine is -1, -1/2, 0, 1/2, or 1. This file
  contains no proof.
*)

needs "Library/transc.ml";;
needs "Library/floor.ml";;

let Q4116459_NIVEN_THEOREM =
  `!theta:real.
     ((?r:real. rational r /\ theta = r * pi) /\
      (?q:real. rational q /\ cos theta = q))
     ==> cos theta = -- &1 \/
         cos theta = --(&1 / &2) \/
         cos theta = &0 \/
         cos theta = &1 / &2 \/
         cos theta = &1`;;
