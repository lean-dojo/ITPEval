(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sameF_upto_le, catalog title "bigops.sameF_upto_le": pointwise
  agreement of arbitrary natural-indexed functions below m is inherited below
  every n <= m. This file contains no proof.
*)

let statement =
  `!f g:num->A.
   !n m:num.
     n <= m
     ==>
     (!i:num. i < m ==> f i = g i)
     ==>
     (!i:num. i < n ==> f i = g i)`;;
