(*
  Statement-only formalization of miniF2F valid problem imo_1964_p1_2. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1964_p1_2: for every natural number n, 7 does not
  divide 2^n + 1. This is a statement-only formalization and contains no proof.
*)

let statement = `!n:num. ~(7 divides (2 EXP n + 1))`;;
