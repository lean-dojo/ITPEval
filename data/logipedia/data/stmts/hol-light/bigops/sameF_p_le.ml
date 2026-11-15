(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sameF_p_le, catalog title "bigops.sameF_p_le": Boolean-selected
  pointwise agreement of arbitrary natural-indexed functions below m is
  inherited below every n <= m. This file contains no proof.
*)

let statement =
  `!p:num->bool.
   !f g:num->A.
   !n m:num.
     n <= m
     ==>
     (!i:num. i < m ==> p i = T ==> f i = g i)
     ==>
     (!i:num. i < n ==> p i = T ==> f i = g i)`;;
