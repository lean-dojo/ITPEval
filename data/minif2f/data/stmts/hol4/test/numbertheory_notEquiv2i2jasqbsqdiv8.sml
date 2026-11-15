(*
  Statement-only formalization of miniF2F test problem
  numbertheory_notEquiv2i2jasqbsqdiv8: being even in both integer coordinates
  is not universally equivalent to their squared sum being a multiple of 8.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val numbertheory_notEquiv2i2jasqbsqdiv8 =
  ``~(!a b : int.
       ((?i : int. ?j : int.
           a = 2 * i /\ b = 2 * j) <=>
        (?k : int.
           a ** 2 + b ** 2 = 8 * k)))``;
