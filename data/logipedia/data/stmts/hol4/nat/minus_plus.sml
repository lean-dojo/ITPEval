(*
  Statement-only formalization of the Logipedia corpus artifact nat.minus_plus
  (catalog title "nat.minus_plus"): iterated truncated subtraction on natural
  numbers equals subtraction by the sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_plus =
  ``!(n : num) (m : num) (p : num).
      (n - m) - p = n - (m + p)``;
