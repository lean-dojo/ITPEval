(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_353. This file
  contains no proof.
*)

let statement =
  `!s:num.
     s = nsum (2010..4018) (\k. k)
     ==> s MOD 2009 = 0`;;
