(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_pi (catalog title "fermat.congruent_pi"): for a
  natural-valued function, the product of its first n values is congruent
  modulo a positive natural p to the product of their residues modulo p.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (x : num) (y : num) (p : num) <=>
      x MOD p = y MOD p``);

val logipedia_fermat_product_def = Define `
  (logipedia_fermat_product 0 (f : num -> num) = 1) /\
  (logipedia_fermat_product (SUC n) f =
     f n * logipedia_fermat_product n f)
`;

val fermat_congruent_pi =
  ``!(f : num -> num) (n : num) (p : num).
      0 < p
      ==>
      logipedia_cong_congruent
        (logipedia_fermat_product n f)
        (logipedia_fermat_product n (\i. f i MOD p))
        p``;
