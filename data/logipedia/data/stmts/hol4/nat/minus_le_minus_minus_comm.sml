(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_le_minus_minus_comm (catalog title
  "nat.minus_le_minus_minus_comm"): for natural numbers a, b, and c with
  c at most b, subtracting b minus c from a equals subtracting b from a plus
  c, using truncated natural-number subtraction. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_le_minus_minus_comm =
  ``!(b : num) (c : num) (a : num).
      c <= b ==> a - (b - c) = (a + c) - b``;
