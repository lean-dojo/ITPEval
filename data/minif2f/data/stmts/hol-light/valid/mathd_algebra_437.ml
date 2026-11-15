(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_437:
  if real numbers x and y have cubes -45 and -101 and an integer n lies
  strictly between them, then n = -4. This file contains no proof.
*)

let statement =
  `!x y:real n:int.
     x pow 3 = -- &45 /\
     y pow 3 = -- &101 /\
     x < real_of_int n /\
     real_of_int n < y
     ==> n = -- &4`;;
