(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5437947 (thousand-theorems__hol4__Q5437947), "Fatou–Lebesgue theorem":
  the lower Lebesgue integral of the pointwise limit inferior of a sequence
  of nonnegative measurable functions is at most the limit inferior of their
  lower Lebesgue integrals. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open measureTheory borelTheory lebesgueTheory;

val lintegral_liminf_le =
  ``!(m : 'a m_space) (f : num -> 'a -> extreal).
      measure_space m /\
      m_space m = UNIV /\
      (!n x. 0 <= f n x) /\
      (!n. f n IN measurable (m_space m,measurable_sets m) Borel)
      ==>
      pos_fn_integral m (\x. liminf (\n. f n x)) <=
      liminf (\n. pos_fn_integral m (f n))``;
