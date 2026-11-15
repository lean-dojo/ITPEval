(*
  Statement-only formalization of miniF2F valid problem imo_1966_p5. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1966_p5: a strictly decreasing quadruple of
  distinct real parameters whose absolute-difference weighted linear system
  has its solution supported at the endpoints. This is a statement-only
  formalization and contains no proof.
*)

let statement =
  `!x a:num->real.
    ~(a 1 = a 2) /\
    ~(a 1 = a 3) /\
    ~(a 1 = a 4) /\
    ~(a 2 = a 3) /\
    ~(a 2 = a 4) /\
    ~(a 3 = a 4) /\
    a 1 > a 2 /\
    a 2 > a 3 /\
    a 3 > a 4 /\
    abs (a 1 - a 2) * x 2 +
      abs (a 1 - a 3) * x 3 +
      abs (a 1 - a 4) * x 4 = &1 /\
    abs (a 2 - a 1) * x 1 +
      abs (a 2 - a 3) * x 3 +
      abs (a 2 - a 4) * x 4 = &1 /\
    abs (a 3 - a 1) * x 1 +
      abs (a 3 - a 2) * x 2 +
      abs (a 3 - a 4) * x 4 = &1 /\
    abs (a 4 - a 1) * x 1 +
      abs (a 4 - a 2) * x 2 +
      abs (a 4 - a 3) * x 3 = &1
    ==> x 2 = &0 /\
        x 3 = &0 /\
        x 1 = &1 / abs (a 1 - a 4) /\
        x 4 = &1 / abs (a 1 - a 4)`;;
