(*
  Statement-only formalization of miniF2F valid artifact amc12a_2009_p15:
  a positive natural number whose weighted sum of powers of the imaginary unit
  from 1 through n is 48 + 49i must equal 97. This file contains no proof.
*)

needs "Complex/complexnumbers.ml";;

let statement =
  `!n:num.
    0 < n /\
    iterate complex_add (1..n) (\k. Cx(&k) * ii pow k) =
      Cx(&48) + Cx(&49) * ii
    ==> n = 97`;;
