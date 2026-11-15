(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.eq_fact_pi_p (catalog title "fermat.eq_fact_pi_p"): for every natural
  number n, n factorial equals the Boolean-filtered product of i + 1 over the
  first n indices, with constant-true filter and multiplicative identity one.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_fermat_bigop_def = Define `
  (logipedia_fermat_bigop 0 (p : num -> bool) (nil : 'a)
      (combine : 'a -> 'a -> 'a) (f : num -> 'a) = nil) /\
  (logipedia_fermat_bigop (SUC n) p nil combine f =
    if p n then
      combine (f n) (logipedia_fermat_bigop n p nil combine f)
    else
      logipedia_fermat_bigop n p nil combine f)
`;

val fermat_eq_fact_pi_p =
  ``!n : num.
      FACT n =
      logipedia_fermat_bigop
        (SUC n - SUC 0)
        (\i. T)
        (SUC 0)
        (\x y : num. x * y)
        (\i. i + SUC 0)``;
