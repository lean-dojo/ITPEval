(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1545 (catalog title "gcd.let_clause_1545"): for natural
  numbers m and n whose greatest common divisor is zero, the stated
  zero-divisibility and zero-product assumptions imply that m is zero.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory dividesTheory gcdTheory;

val gcd_let_clause_1545 =
  ``!(m : num) (n : num).
      gcd m n = 0 ==>
      divides 0 n ==>
      !(q1 : num).
        n = 0 * q1 ==>
        divides 0 m ==>
        !(q2 : num).
          m = 0 * q2 ==>
          m = 0``;
