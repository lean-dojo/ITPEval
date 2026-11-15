(*
  Statement-only formalization of Logipedia corpus artifact
  sigma_pi.exp_pi_l (catalog title "sigma_pi.exp_pi_l"): multiplying the
  product of the values f i over the first n natural indices by a raised to n
  equals the product with a multiplied into every term.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_sigma_pi_product_def = new_recursive_definition {
  name = "logipedia_sigma_pi_product_def",
  rec_axiom = prim_recTheory.num_Axiom,
  def =
    ``(logipedia_sigma_pi_product 0 (f : num -> num) = 1) /\
      (logipedia_sigma_pi_product (SUC n) f =
        f n * logipedia_sigma_pi_product n f)``
};

val sigma_pi_exp_pi_l =
  ``!(n : num) (a : num) (f : num -> num).
      a EXP n * logipedia_sigma_pi_product n f =
      logipedia_sigma_pi_product n (\i. a * f i)``;
