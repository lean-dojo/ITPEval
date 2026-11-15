(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b1
  (putnambench__hol-light__putnam_2020_b1): the residue modulo 2020 of an
  alternating cubic sum weighted by binary digit sums. This file contains no
  proof.
*)

let statement =
  `!d:num->num. !S:int.
     (!n:num.
        d n =
        if n = 0 then 0
        else n MOD 2 + d (n DIV 2)) /\
     S =
     isum (1..2020)
          (\k:num. (-- &1) pow (d k) * (&k) pow 3)
     ==>
     (S == &1990) (mod &2020)`;;
