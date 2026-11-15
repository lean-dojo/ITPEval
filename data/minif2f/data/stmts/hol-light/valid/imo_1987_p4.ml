(*
  Statement-only formalization of miniF2F valid problem imo_1987_p4. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1987_p4: every function from the natural numbers
  to themselves has an input n for which its second iterate differs from
  n + 1987. This is a statement-only formalization and contains no proof.
*)

let imo_1987_p4 =
  `!f:num->num. ?n:num. ~(f (f n) = n + 1987)`;;
