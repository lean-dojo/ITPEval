(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sub0_to_false, catalog title "bigops.sub0_to_false": if the target
  bound of the source's selected-index embedding relation is zero, every
  Boolean selector below the source bound is false. This file contains no
  proof.
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
  `!h k:num->num.
   !n1 n2:num.
   !p1 p2:num->bool.
   !f1 f2:num->num.
     n1 = 0
     ==>
     logipedia_bigops_sub_hk h k n2 n1 p2 p1 f2 f1
     ==>
     !i:num. i < n2 ==> p2 i = F`;;
