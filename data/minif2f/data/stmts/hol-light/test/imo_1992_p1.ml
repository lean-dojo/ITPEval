(*
  Statement-only formalization of miniF2F test problem imo_1992_p1. This file contains no proof.
*)

let statement =
  `!p q r:int.
     &1 < p /\ p < q /\ q < r /\
     (p - &1) * (q - &1) * (r - &1) divides (p * q * r - &1)
     ==> (p = &2 /\ q = &4 /\ r = &8) \/
         (p = &3 /\ q = &5 /\ r = &15)`;;
