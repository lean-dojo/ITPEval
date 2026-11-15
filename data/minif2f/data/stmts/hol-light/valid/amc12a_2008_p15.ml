(*
  Statement-only formalization of miniF2F valid problem amc12a_2008_p15:
  for the natural number k = 2008^2 + 2^2008, the remainder modulo 10 of
  k^2 + 2^k is 6. This file contains no proof.
*)

let statement =
  `!k:num.
     k = 2008 EXP 2 + 2 EXP 2008
     ==> (k EXP 2 + 2 EXP k) MOD 10 = 6`;;
