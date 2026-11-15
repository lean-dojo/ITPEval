(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_690:
  314 is the least positive natural number with remainders 2, 4, 6, and 8
  modulo 3, 5, 7, and 9, respectively. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_690 =
  ``(0 < (314 : num) /\
      314 MOD 3 = 2 /\
      314 MOD 5 = 4 /\
      314 MOD 7 = 6 /\
      314 MOD 9 = 8) /\
    (!a : num.
      (0 < a /\
       a MOD 3 = 2 /\
       a MOD 5 = 4 /\
       a MOD 7 = 6 /\
       a MOD 9 = 8)
      ==>
      314 <= a)``;
