(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q193910, "Euler's theorem": if natural numbers x and n are coprime, then
  x raised to Euler's totient of n is congruent to 1 modulo n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory numberTheory;

val q193910_euler_s_theorem =
  ``!x : num.
      !n : num.
        coprime x n ==>
        (x EXP (totient n)) MOD n = (1 MOD n)``;
