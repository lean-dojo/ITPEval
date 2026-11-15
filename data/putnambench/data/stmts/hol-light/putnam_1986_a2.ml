(*
  Statement-only formalization of PutnamBench artifact putnam_1986_a2:
  the units digit of the integer part of 10^20000 divided by 10^100 + 3
  is 3. This file contains no proof.
*)

let statement =
  `((10 EXP 20000) DIV (10 EXP 100 + 3)) MOD 10 = 3`;;
