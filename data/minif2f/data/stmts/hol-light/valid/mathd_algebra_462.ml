(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_462. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_462: over the real numbers, the product
  of the sum and difference of one half and one third is five thirty-sixths.
  This is a statement-only formalization and contains no proof.
*)

let statement =
  `(((&1:real) / &2 + &1 / &3) * (&1 / &2 - &1 / &3) = &5 / &36)`;;
