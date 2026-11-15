(*
  Statement-only formalization of miniF2F valid problem imo_1964_p1_1. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1964_p1_1: if 7 divides 2^n - 1 for a natural
  number n, then 3 divides n. This is a statement-only formalization and
  contains no proof.
*)

let statement =
  `!n:num. 7 divides (2 EXP n - 1) ==> 3 divides n`;;
