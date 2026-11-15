(*
  Statement-only formalization of Logipedia corpus artifact bigops.sub_lt,
  catalog title "bigops.sub_lt": an identity selected-index embedding of a
  Boolean-filtered natural-number family from any bound n into a bound m
  whenever n <= m. This file contains no proof.
*)

let logipedia_bigops_sub_hk = new_definition
  `logipedia_bigops_sub_hk
       (h:num->num) (k:num->num) (n1:num) (n2:num)
       (p1:num->bool) (p2:num->bool) (f1:num->num) (f2:num->num) <=>
     !i:num.
       i < n1
       ==>
       p1 i = T
       ==>
       (h i < n2 /\ p2 (h i) = T) /\ k (h i) = i`;;

let statement =
  `!e:num->num.
   !p:num->bool.
   !n m:num.
     n <= m
     ==>
     logipedia_bigops_sub_hk
       (\x:num. x) (\x:num. x) n m p p e e`;;
