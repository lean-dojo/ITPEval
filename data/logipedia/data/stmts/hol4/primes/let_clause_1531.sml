(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.let_clause_1531 (catalog title "primes.let_clause_1531"): for natural
  numbers n and m, positivity of m, divisibility of m by n, and the equality
  m = n * 0 imply m = 0, uniformly for every natural d. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_let_clause_1531 =
  ``!(n : num) (m : num).
      0 < m ==>
      divides n m ==>
      !d : num.
        m = n * 0 ==>
        m = 0``;
