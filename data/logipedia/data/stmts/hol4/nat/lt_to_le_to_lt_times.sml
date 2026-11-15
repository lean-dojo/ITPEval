(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_le_to_lt_times (catalog title "nat.lt_to_le_to_lt_times"): for
  natural numbers n, m, p, and q, n less than m, p less than or equal to q,
  and zero less than q imply n times p is less than m times q. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_to_le_to_lt_times =
  ``!(n : num) (m : num) (p : num) (q : num).
      n < m ==>
      p <= q ==>
      0 < q ==>
      n * p < m * q``;
