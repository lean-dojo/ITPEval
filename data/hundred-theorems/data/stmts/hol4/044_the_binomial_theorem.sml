(*
  Statement-only formalization of "The Binomial Theorem" from Hundred Theorems item 044.
  For natural numbers n, x, and y, the nth power of x + y is the sum over k = 0,...,n
  of the binomial coefficient times x^(n-k) and y^k. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory listTheory;

val binomial_theorem =
  ``!n x y : num.
      (x + y) ** n =
      SUM
        (GENLIST
           (\k. binomial n k * x ** (n - k) * y ** k)
           (SUC n))``;
