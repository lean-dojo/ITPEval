(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_552:
  the finite set of gcd values of 12x + 7 and 5x + 2 over positive natural
  numbers has sum 12. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory pred_setTheory;

val mathd_numbertheory_552 =
  ``!f g h : num -> num.
      (!x : num. 0 < x ==> f x = 12 * x + 7) /\
      (!x : num. 0 < x ==> g x = 5 * x + 2) /\
      (!x : num. 0 < x ==> h x = gcd (f x) (g x)) /\
      FINITE (IMAGE h {x : num | 0 < x})
      ==>
      SIGMA (\k : num. k) (IMAGE h {x : num | 0 < x}) = 12``;
