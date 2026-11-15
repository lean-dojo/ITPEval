(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_gcd_nm (catalog title "gcd.divides_gcd_nm"): for all natural
  numbers n and m, their greatest common divisor divides both m and n. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory;

val gcd_divides_gcd_nm =
  ``!(n : num) (m : num).
      divides (gcd n m) m /\
      divides (gcd n m) n``;
