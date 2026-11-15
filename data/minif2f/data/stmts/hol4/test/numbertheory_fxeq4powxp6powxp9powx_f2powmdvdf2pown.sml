(*
  Statement-only formalization of miniF2F test problem
  numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown: divisibility between
  f (2^m) and f (2^n) for f x = 4^x + 6^x + 9^x. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown =
  ``!m n : num. !f : num -> num.
      (!x : num. f x = 4 EXP x + 6 EXP x + 9 EXP x) /\
      0 < m /\ 0 < n /\
      m <= n
      ==>
      divides (f (2 EXP m)) (f (2 EXP n))``;
