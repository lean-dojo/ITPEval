(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b5
  (putnambench__hol-light__putnam_2025_b5): the number of descents among the
  least positive modular inverses of consecutive nonzero residues modulo a
  prime greater than three exceeds p/4 - 1. This file contains no proof.
*)

let statement =
  `!p:num.
     prime p /\ 3 < p
     ==>
     let modular_inverse =
       \k:num.
         @i:num. i < p /\ (k * i) MOD p = 1 in
     (&p:real) / &4 - &1 <
     &(CARD
         {k:num |
            k IN 1..(p - 2) /\
            modular_inverse (k + 1) < modular_inverse k})`;;
