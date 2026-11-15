(*
  Statement-only formalization of miniF2F test problem induction_nfactltnexpnm1ngt3: the
  factorial bound n! < n^(n - 1) for natural numbers n >= 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val induction_nfactltnexpnm1ngt3 =
  ``!n : num. 3 <= n ==> FACT n < n EXP (n - 1)``;
