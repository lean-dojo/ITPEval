(*
  Statement-only formalization of miniF2F valid problem amc12a_2008_p2:
  for a real number x satisfying x times (1/2 + 2/3) equals 1, x equals
  6/7. This file contains no proof.
*)

let statement =
  `!x:real.
     x * (&1 / &2 + &2 / &3) = &1
     ==> x = &6 / &7`;;
