(*
  Statement-only formalization of Logipedia corpus artifact
  sigma_pi.exp_pi_bc (catalog title "sigma_pi.exp_pi_bc"): multiplying the
  Boolean-filtered product of the shifted values f (i + b) over c - b indices
  by a raised to c - b equals the product with a multiplied into every term.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_sigma_pi_bigop_def = Define `
  (logipedia_sigma_pi_bigop 0 (p : num -> bool) (nil : 'a)
      (combine : 'a -> 'a -> 'a) (f : num -> 'a) = nil) /\
  (logipedia_sigma_pi_bigop (SUC n) p nil combine f =
    if p n then
      combine (f n) (logipedia_sigma_pi_bigop n p nil combine f)
    else
      logipedia_sigma_pi_bigop n p nil combine f)
`;

val sigma_pi_exp_pi_bc =
  ``!(a : num) (b : num) (c : num) (f : num -> num).
      a EXP (c - b) *
        logipedia_sigma_pi_bigop
          (c - b)
          (\i. T)
          (SUC 0)
          (\x y : num. x * y)
          (\i. f (i + b)) =
      logipedia_sigma_pi_bigop
        (c - b)
        (\i. T)
        (SUC 0)
        (\x y : num. x * y)
        (\i. a * f (i + b))``;
