(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b6:
  the cubing permutation of residue classes modulo an odd prime congruent to
  two modulo three is even exactly when the prime is three modulo four. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory;

val putnam_2012_b6 =
  ``!p : num. !P : num -> num.
      ODD p /\
      prime p /\
      p MOD 3 = 2 /\
      P permutes count p /\
      (!i : num. i < p ==> P i = (i EXP 3) MOD p)
      ==>
      (evenperm P <=> p MOD 4 = 3)``;
