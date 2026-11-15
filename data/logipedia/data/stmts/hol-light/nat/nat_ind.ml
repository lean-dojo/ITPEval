(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_ind,
  catalog title "nat.nat_ind": mathematical induction for arbitrary
  predicates on the natural numbers. This file contains no proof.
*)

let statement =
  `!Q:num->bool.
     Q 0 ==>
     (!x:num. Q x ==> Q (SUC x)) ==>
     !x:num. Q x`;;
