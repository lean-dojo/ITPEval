(*
  Statement-only formalization of miniF2F valid problem imo_2006_p3. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_2006_p3: a cyclic quartic inequality over the
  real numbers with a square-root constant. This is a statement-only
  formalization and contains no proof.
*)

let statement =
  `!a b c:real.
     a * b * (a pow 2 - b pow 2) +
     b * c * (b pow 2 - c pow 2) +
     c * a * (c pow 2 - a pow 2) <=
     (&9 * sqrt (&2)) / &32 *
     (a pow 2 + b pow 2 + c pow 2) pow 2`;;
