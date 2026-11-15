(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_269:
  a closed modular-arithmetic computation involving powers of 2005. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_269 =
  ``((2005 : num) EXP 2 + 2005 EXP 0 + 2005 EXP 0 + 2005 EXP 5) MOD 100 = 52``;
