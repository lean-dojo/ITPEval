(*
  Statement-only formalization of miniF2F test problem imo_1962_p2. This file contains no proof.
*)

let statement =
  `!x:real.
     &0 <= &3 - x /\
     &0 <= x + &1 /\
     &1 / &2 < sqrt (&3 - x) - sqrt (x + &1)
     ==> -- &1 <= x /\ x < &1 - sqrt (&31) / &8`;;
