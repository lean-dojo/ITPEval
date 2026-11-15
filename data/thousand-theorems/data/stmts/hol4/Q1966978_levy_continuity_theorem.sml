(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1966978 (thousand-theorems__hol4__Q1966978), "Lévy continuity theorem":
  weak convergence of Borel probability measures on a finite-dimensional
  real inner-product space is equivalent to pointwise convergence of their
  characteristic functions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory iterateTheory realTheory transcTheory;
open complexTheory topologyTheory real_topologyTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory lebesgueTheory;
open probabilityTheory;

val q1966978_add_comm_group_def = new_definition (
  "q1966978_add_comm_group_def",
  ``q1966978_add_comm_group
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero)``);

val q1966978_real_inner_product_space_def = new_definition (
  "q1966978_real_inner_product_space_def",
  ``q1966978_real_inner_product_space
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real) <=>
      q1966978_add_comm_group zero add neg /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!x. neg x = smul (-1) x) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!a x y. inner (smul a x) y = a * inner x y) /\
      (!x y. inner x y = inner y x) /\
      (!x. 0 <= inner x x) /\
      (!x. (inner x x = 0) <=> (x = zero)) /\
      (!x. norm x = sqrt (inner x x)) /\
      ?n : num.
        ?basis : num -> 'v.
          (!j k.
            j IN count n /\ k IN count n ==>
            inner (basis j) (basis k) =
              if j = k then 1 else 0) /\
          !x.
            x =
              ITSET
                (\k acc. add (smul (inner x (basis k)) (basis k)) acc)
                (count n) zero``);

val q1966978_metric_open_def = new_definition (
  "q1966978_metric_open_def",
  ``q1966978_metric_open
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (s : 'v set) <=>
      !x.
        x IN s ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            norm (add y (neg x)) < epsilon ==> y IN s``);

val q1966978_probability_measure_def = new_definition (
  "q1966978_probability_measure_def",
  ``q1966978_probability_measure
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (m : 'v m_space) <=>
      prob_space m /\
      m_space m = UNIV /\
      measurable_sets m =
        sigma_sets UNIV {s | q1966978_metric_open add neg norm s}``);

val q1966978_bounded_continuous_def = new_definition (
  "q1966978_bounded_continuous_def",
  ``q1966978_bounded_continuous
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (f : 'v -> real) <=>
      (!x epsilon.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y.
            norm (add y (neg x)) < delta ==>
            abs (f y - f x) < epsilon) /\
      ?C : real.
        0 <= C /\ !x. abs (f x) <= C``);

val q1966978_real_integral_def = new_definition (
  "q1966978_real_integral_def",
  ``q1966978_real_integral (m : 'v m_space) (f : 'v -> real) =
      real (integral m (\x. Normal (f x)))``);

val q1966978_tendsto_real_def = new_definition (
  "q1966978_tendsto_real_def",
  ``q1966978_tendsto_real (u : num -> real) (ell : real) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num.
            N <= n ==> abs (u n - ell) < epsilon``);

val q1966978_tendsto_complex_def = new_definition (
  "q1966978_tendsto_complex_def",
  ``q1966978_tendsto_complex (u : num -> complex) (ell : complex) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num.
            N <= n ==> modu (u n - ell) < epsilon``);

val q1966978_weak_tendsto_def = new_definition (
  "q1966978_weak_tendsto_def",
  ``q1966978_weak_tendsto
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real)
      (mu : num -> 'v m_space) (mu0 : 'v m_space) <=>
      !f : 'v -> real.
        q1966978_bounded_continuous add neg norm f ==>
        q1966978_tendsto_real
          (\n. q1966978_real_integral (mu n) f)
          (q1966978_real_integral mu0 f)``);

val q1966978_char_fun_def = new_definition (
  "q1966978_char_fun_def",
  ``q1966978_char_fun
      (inner : 'v -> 'v -> real) (m : 'v m_space) (t : 'v) =
      complex_of_real
        (q1966978_real_integral m (\x. cos (inner x t))) +
      i * complex_of_real
        (q1966978_real_integral m (\x. sin (inner x t)))``);

val levy_continuity_theorem =
  ``!(zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real)
      (mu : num -> 'v m_space) (mu0 : 'v m_space).
      q1966978_real_inner_product_space
        zero add neg smul inner norm /\
      (!n. q1966978_probability_measure add neg norm (mu n)) /\
      q1966978_probability_measure add neg norm mu0
      ==>
      (q1966978_weak_tendsto add neg norm mu mu0 <=>
       !t : 'v.
         q1966978_tendsto_complex
           (\n. q1966978_char_fun inner (mu n) t)
           (q1966978_char_fun inner mu0 t))``;
