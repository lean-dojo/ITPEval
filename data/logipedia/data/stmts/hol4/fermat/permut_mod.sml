(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.permut_mod (catalog title "fermat.permut_mod"): multiplication by a
  natural a modulo a prime p permutes the inclusive natural interval from
  zero through PRE p when p does not divide a. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_permutation_permut_def = new_definition (
  "logipedia_permutation_permut_def",
  ``logipedia_permutation_permut (f : num -> num) (m : num) <=>
      (!i : num. i <= m ==> f i <= m) /\
      !i j : num.
        i <= m ==>
        j <= m ==>
        f i = f j ==>
        i = j``);

val fermat_permut_mod =
  ``!p : num.
      !a : num.
        prime p ==>
        ~divides p a ==>
        logipedia_permutation_permut
          (\n. (a * n) MOD p)
          (PRE p)``;
