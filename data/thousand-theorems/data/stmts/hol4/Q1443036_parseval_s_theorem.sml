(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1443036 (thousand-theorems__hol4__Q1443036), "Parseval's theorem":
  for every complex L2 function on a positive-period additive circle, the
  bilateral sum of squared Fourier-coefficient norms equals its normalized
  squared L2 norm. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory intrealTheory pred_setTheory;
open realTheory transcTheory complexTheory seqTheory real_topologyTheory;
open extrealTheory measureTheory borelTheory lebesgueTheory;

val q1443036_domain_def = new_definition (
  "q1443036_domain_def",
  ``q1443036_domain (period : real) =
      interval [(0 : real),period]``);

val q1443036_l2_on_circle_def = new_definition (
  "q1443036_l2_on_circle_def",
  ``q1443036_l2_on_circle
      (period : real) (f : real -> complex) <=>
      (\x.
        Normal (RE (f x)) *
        indicator_fn (q1443036_domain period) x) IN
        measurable (m_space lborel,measurable_sets lborel) Borel /\
      (\x.
        Normal (IM (f x)) *
        indicator_fn (q1443036_domain period) x) IN
        measurable (m_space lborel,measurable_sets lborel) Borel /\
      integrable lborel
        (\x.
          Normal ((modu (f x)) pow 2) *
          indicator_fn (q1443036_domain period) x)``);

val q1443036_complex_integral_on_def = new_definition (
  "q1443036_complex_integral_on_def",
  ``q1443036_complex_integral_on
      (s : real set) (g : real -> complex) =
      complex_of_real
        (real
          (integral lborel
            (\x. Normal (RE (g x)) * indicator_fn s x))) +
      i *
        complex_of_real
          (real
            (integral lborel
              (\x. Normal (IM (g x)) * indicator_fn s x)))``);

val q1443036_integer_index_def = new_definition (
  "q1443036_integer_index_def",
  ``q1443036_integer_index (n : num) =
      if EVEN n then
        int_of_num (n DIV 2)
      else
        -(int_of_num (n DIV 2 + 1))``);

val q1443036_fourier_coefficient_def = new_definition (
  "q1443036_fourier_coefficient_def",
  ``q1443036_fourier_coefficient
      (period : real) (f : real -> complex) (k : int) =
      complex_of_real (1 / period) *
      q1443036_complex_integral_on
        (q1443036_domain period)
        (\x.
          complex_exp
            (-(i *
              complex_of_real
                (2 * pi * real_of_int k * x / period))) *
          f x)``);

val parseval_s_theorem =
  ``!(period : real) (f : real -> complex).
      0 < period /\
      q1443036_l2_on_circle period f
      ==>
      suminf
        (\n : num.
          (modu
            (q1443036_fourier_coefficient
              period f (q1443036_integer_index n))) pow 2) =
      (1 / period) *
        real
          (integral lborel
            (\x.
              Normal ((modu (f x)) pow 2) *
              indicator_fn (q1443036_domain period) x))``;
