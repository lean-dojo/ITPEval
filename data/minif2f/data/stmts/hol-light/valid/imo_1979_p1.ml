(*
  Statement-only formalization of miniF2F valid problem imo_1979_p1. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1979_p1: if the alternating harmonic sum from
  1 through 1319 equals p/q for naturals p and positive q, then 1979 divides
  p. This is a statement-only formalization and contains no proof.
*)

let statement = `!p q:num.
    0 < q /\
    sum (1..1319) (\k:num. (-- &1) pow (k + 1) * (&1 / &k)) =
      &p / &q
    ==> 1979 divides p`;;
