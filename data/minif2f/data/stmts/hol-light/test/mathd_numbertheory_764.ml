(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_764. This file
  contains no proof.
*)

let statement =
  `!p:num a:num->num.
     prime p /\ 7 <= p /\
     (!k. k IN (1..(p - 1)) ==> (a k * k) MOD p = 1)
     ==> (nsum (1..(p - 2)) (\k. a k * a (k + 1))) MOD p = 2`;;
