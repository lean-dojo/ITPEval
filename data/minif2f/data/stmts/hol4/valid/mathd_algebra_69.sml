(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_69: a natural-number
  row-and-seat product system determines the number of rows as 25. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_algebra_69 =
  ``!rows seats : num.
      rows * seats = 450 /\
      (rows + 5) * (seats - 3) = 450
      ==>
      rows = 25``;
