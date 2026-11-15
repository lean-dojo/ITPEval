(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_629:
  18 is the least positive natural number t for which lcm(12,t)^3 = (12*t)^2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_629 =
  ``0 < (18 : num) /\
    (lcm 12 18) EXP 3 = (12 * 18) EXP 2 /\
    (!t : num.
       (0 < t /\
        (lcm 12 t) EXP 3 = (12 * t) EXP 2)
       ==>
       18 <= t)``;
