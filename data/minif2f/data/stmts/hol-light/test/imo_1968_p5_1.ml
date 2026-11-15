(*
  Statement-only formalization of miniF2F test artifact imo_1968_p5_1:
  a real-valued function satisfying the given square-root shift recurrence
  with positive shift has a positive period. This file contains no proof.
*)

let statement =
  `!a:real f:real->real.
     &0 < a /\
     (!x.
        f (x + a) =
          &1 / &2 +
          (if &0 <= f x - (f x) pow 2
           then sqrt (f x - (f x) pow 2)
           else &0))
     ==> ?b:real. &0 < b /\ !x. f (x + b) = f x`;;
