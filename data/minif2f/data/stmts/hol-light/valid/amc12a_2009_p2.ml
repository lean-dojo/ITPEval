(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p2:
  evaluating the finite continued fraction 1 + 1/(1 + 1/(1 + 1)) as 5/3.
  This file contains no proof.
*)

let statement =
  `(&1:real) + &1 / (&1 + &1 / (&1 + &1)) = &5 / &3`;;
