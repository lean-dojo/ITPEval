(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_509. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_509: a real expression involving
  square roots of 80, 845, 45, and 5 has square root 13/6. This is a
  statement-only formalization and contains no proof.
*)

let statement =
  `sqrt ((&5 / sqrt (&80) + sqrt (&845) / &9 + sqrt (&45)) /
         sqrt (&5)) =
   &13 / &6`;;
