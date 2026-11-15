(*
  Statement-only formalization of Logipedia corpus artifact bigops.sub_hkO,
  catalog title "bigops.sub_hkO": a zero source bound implies the selected-index
  embedding relation between two Boolean-filtered natural-number families.
  This file contains no proof.
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
     logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2`;;
