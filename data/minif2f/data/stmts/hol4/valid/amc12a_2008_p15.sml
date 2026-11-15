(*
  Statement-only formalization of miniF2F valid problem amc12a_2008_p15: the last digit of
  k squared plus 2 to the k when k is 2008 squared plus 2 to the 2008. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val amc12a_2008_p15 =
  ``!k : num.
      k = 2008 EXP 2 + 2 EXP 2008 ==>
      (k EXP 2 + 2 EXP k) MOD 10 = 6``;
