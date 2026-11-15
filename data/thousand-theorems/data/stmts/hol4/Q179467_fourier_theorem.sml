(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q179467 (thousand-theorems__hol4__Q179467), "Fourier theorem": Fourier
  inversion for integrable functions from a finite-dimensional real
  inner-product space to a complete complex normed space, at continuity
  points and globally for continuous functions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory complexTheory;
open topologyTheory real_topologyTheory extrealTheory sigma_algebraTheory;
open measureTheory borelTheory lebesgueTheory;

val q179467_add_comm_group_def = new_definition (
  "q179467_add_comm_group_def",
  ``q179467_add_comm_group
      (zero : 'a) (add : 'a -> 'a -> 'a) (neg : 'a -> 'a) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero)``);

val q179467_real_inner_product_space_def = new_definition (
  "q179467_real_inner_product_space_def",
  ``q179467_real_inner_product_space
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real) <=>
      q179467_add_comm_group zero add neg /\
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

val q179467_complex_normed_space_def = new_definition (
  "q179467_complex_normed_space_def",
  ``q179467_complex_normed_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real) <=>
      q179467_add_comm_group zero add neg /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!x. neg x = smul (-1) x) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = modu a * norm x)``);

val q179467_tendsto_def = new_definition (
  "q179467_tendsto_def",
  ``q179467_tendsto
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) (ell : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num.
            N <= n ==> norm (add (u n) (neg ell)) < epsilon``);

val q179467_cauchy_def = new_definition (
  "q179467_cauchy_def",
  ``q179467_cauchy
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !p q : num.
            N <= p /\ N <= q ==>
            norm (add (u p) (neg (u q))) < epsilon``);

val q179467_complete_def = new_definition (
  "q179467_complete_def",
  ``q179467_complete
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) <=>
      !u : num -> 'a.
        q179467_cauchy add neg norm u ==>
        ?ell : 'a. q179467_tendsto add neg norm u ell``);

val q179467_metric_open_def = new_definition (
  "q179467_metric_open_def",
  ``q179467_metric_open
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (s : 'v set) <=>
      !x.
        x IN s ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            norm (add y (neg x)) < epsilon ==> y IN s``);

val q179467_volume_measure_def = new_definition (
  "q179467_volume_measure_def",
  ``q179467_volume_measure
      (m : 'v m_space)
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real) <=>
      measure_space m /\
      m_space m = UNIV /\
      measurable_sets m =
        sigma_sets UNIV {s | q179467_metric_open add neg norm s} /\
      ?n : num.
        ?basis : num -> 'v.
          (!j k.
            j IN count n /\ k IN count n ==>
            inner (basis j) (basis k) =
              if j = k then 1 else 0) /\
          (!x.
            x =
              ITSET
                (\k acc. add (smul (inner x (basis k)) (basis k)) acc)
                (count n) zero) /\
          !a b : num -> real.
            (!k. k IN count n ==> a k <= b k) ==>
            measure m
              {x |
                !k.
                  k IN count n ==>
                  a k <= inner x (basis k) /\
                  inner x (basis k) < b k} =
            Normal
              (ITSET
                (\k acc. (b k - a k) * acc)
                (count n) 1)``);

val q179467_measurable_simple_def = new_definition (
  "q179467_measurable_simple_def",
  ``q179467_measurable_simple
      (m : 'v m_space) (s : 'v -> 'e) <=>
      FINITE (IMAGE s UNIV) /\
      !y : 'e. {x | s x = y} IN measurable_sets m``);

val q179467_strongly_measurable_def = new_definition (
  "q179467_strongly_measurable_def",
  ``q179467_strongly_measurable
      (m : 'v m_space)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : 'v -> 'e) <=>
      ?s : num -> 'v -> 'e.
        (!n. q179467_measurable_simple m (s n)) /\
        !x. q179467_tendsto add neg norm (\n. s n x) (f x)``);

val q179467_bochner_integrable_def = new_definition (
  "q179467_bochner_integrable_def",
  ``q179467_bochner_integrable
      (m : 'v m_space)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : 'v -> 'e) <=>
      ?g : 'v -> 'e.
        q179467_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x)``);

val q179467_simple_integral_def = new_definition (
  "q179467_simple_integral_def",
  ``q179467_simple_integral
      (m : 'v m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : complex -> 'e -> 'e) (s : 'v -> 'e) =
      ITSET
        (\y acc.
          add
            (smul
              (complex_of_real (real (measure m {x | s x = y}))) y)
            acc)
        (IMAGE s UNIV DELETE zero) zero``);

val q179467_bochner_approximates_def = new_definition (
  "q179467_bochner_approximates_def",
  ``q179467_bochner_approximates
      (m : 'v m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : 'v -> 'e) (s : num -> 'v -> 'e) (ell : 'e) <=>
      ?g : 'v -> 'e.
        q179467_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x) /\
        (!n. q179467_measurable_simple m (s n)) /\
        (!n. integrable m (Normal o (\x. norm (s n x)))) /\
        (!n.
          integrable m
            (Normal o (\x. norm (add (s n x) (neg (g x)))))) /\
        (((\n.
            real
              (integral m
                (Normal o
                  (\x. norm (add (s n x) (neg (g x))))))) -->
          0) sequentially) /\
        q179467_tendsto add neg norm
          (\n. q179467_simple_integral m zero add smul (s n))
          ell``);

val q179467_bochner_integral_def = new_definition (
  "q179467_bochner_integral_def",
  ``q179467_bochner_integral
      (m : 'v m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : 'v -> 'e) =
      if q179467_complete add neg norm /\
         q179467_bochner_integrable m add neg norm f
      then
        @ell : 'e.
          ?s : num -> 'v -> 'e.
            q179467_bochner_approximates
              m zero add neg smul norm f s ell
      else
        zero``);

val q179467_continuous_at_def = new_definition (
  "q179467_continuous_at_def",
  ``q179467_continuous_at
      (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (normV : 'v -> real)
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (f : 'v -> 'e) (v : 'v) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !w.
            normV (addV w (negV v)) < delta ==>
            normE (addE (f w) (negE (f v))) < epsilon``);

val q179467_continuous_def = new_definition (
  "q179467_continuous_def",
  ``q179467_continuous
      (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (normV : 'v -> real)
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (f : 'v -> 'e) <=>
      !v.
        q179467_continuous_at
          addV negV normV addE negE normE f v``);

val q179467_fourier_def = new_definition (
  "q179467_fourier_def",
  ``q179467_fourier
      (m : 'v m_space) (inner : 'v -> 'v -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : 'v -> 'e) (w : 'v) =
      q179467_bochner_integral
        m zeroE addE negE smulE normE
        (\x.
          smulE
            (complex_exp
              (-(i * complex_of_real (2 * pi * inner w x))))
            (f x))``);

val q179467_fourier_inv_def = new_definition (
  "q179467_fourier_inv_def",
  ``q179467_fourier_inv
      (m : 'v m_space) (inner : 'v -> 'v -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : 'v -> 'e) (v : 'v) =
      q179467_bochner_integral
        m zeroE addE negE smulE normE
        (\w.
          smulE
            (complex_exp
              (i * complex_of_real (2 * pi * inner w v)))
            (f w))``);

val fourier_inversion =
  ``!(m : 'v m_space)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (normV : 'v -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : 'v -> 'e) (v : 'v).
      q179467_real_inner_product_space
        zeroV addV negV smulV inner normV /\
      q179467_volume_measure
        m zeroV addV negV smulV inner normV /\
      q179467_complex_normed_space zeroE addE negE smulE normE /\
      q179467_complete addE negE normE /\
      q179467_bochner_integrable m addE negE normE f /\
      q179467_bochner_integrable m addE negE normE
        (q179467_fourier
          m inner zeroE addE negE smulE normE f) /\
      q179467_continuous_at
        addV negV normV addE negE normE f v
      ==>
      q179467_fourier_inv
        m inner zeroE addE negE smulE normE
        (q179467_fourier
          m inner zeroE addE negE smulE normE f) v =
      f v``;

val continuous_fourier_inversion =
  ``!(m : 'v m_space)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (normV : 'v -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : 'v -> 'e).
      q179467_real_inner_product_space
        zeroV addV negV smulV inner normV /\
      q179467_volume_measure
        m zeroV addV negV smulV inner normV /\
      q179467_complex_normed_space zeroE addE negE smulE normE /\
      q179467_complete addE negE normE /\
      q179467_continuous
        addV negV normV addE negE normE f /\
      q179467_bochner_integrable m addE negE normE f /\
      q179467_bochner_integrable m addE negE normE
        (q179467_fourier
          m inner zeroE addE negE smulE normE f)
      ==>
      q179467_fourier_inv
        m inner zeroE addE negE smulE normE
        (q179467_fourier
          m inner zeroE addE negE smulE normE f) =
      f``;
