(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b6
  (putnambench__hol-light__putnam_2017_b6): counting ordered 64-tuples of
  distinct integers from 1 through 2017 whose stated weighted sum is divisible
  by 2017. This file contains no proof.
*)

let statement =
  `CARD
     {x:num list |
        LENGTH x = 64 /\
        (!i:num. i < 64 ==> 1 <= EL i x /\ EL i x <= 2017) /\
        (!i j:num.
           i < 64 /\ j < 64 /\ EL i x = EL j x
           ==> i = j) /\
        2017 divides
          nsum (0..63)
            (\i:num. if i < 2 then EL i x else i * EL i x)} =
   FACT 2016 DIV FACT 1953 - FACT 63 * 2016`;;
