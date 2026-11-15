(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2096184, "Plancherel theorem": the Fourier transform preserves the
  integral inner product of Schwartz functions on a finite-dimensional real
  inner-product space with values in a complex Hilbert space. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory transcTheory;
open complexTheory topologyTheory real_topologyTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory lebesgueTheory;

val q2096184_add_comm_group_def = new_definition (
  "q2096184_add_comm_group_def",
  ``q2096184_add_comm_group
      (zero : 'a) (add : 'a -> 'a -> 'a) (neg : 'a -> 'a) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero)``);

val q2096184_orthonormal_basis_def = new_definition (
  "q2096184_orthonormal_basis_def",
  ``q2096184_orthonormal_basis
      (zero : 'v) (add : 'v -> 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (n : num) (basis : num -> 'v) <=>
      (!j k.
        j IN count n /\ k IN count n ==>
        inner (basis j) (basis k) = if j = k then 1 else 0) /\
      !x.
        x =
          ITSET
            (\k acc. add (smul (inner x (basis k)) (basis k)) acc)
            (count n) zero``);

val q2096184_real_inner_product_space_def = new_definition (
  "q2096184_real_inner_product_space_def",
  ``q2096184_real_inner_product_space
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real) <=>
      q2096184_add_comm_group zero add neg /\
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
      ?n basis. q2096184_orthonormal_basis zero add smul inner n basis``);

val q2096184_cauchy_def = new_definition (
  "q2096184_cauchy_def",
  ``q2096184_cauchy
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !p q : num.
            N <= p /\ N <= q ==>
            norm (add (u p) (neg (u q))) < epsilon``);

val q2096184_tendsto_def = new_definition (
  "q2096184_tendsto_def",
  ``q2096184_tendsto
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) (ell : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num.
            N <= n ==> norm (add (u n) (neg ell)) < epsilon``);

val q2096184_complete_def = new_definition (
  "q2096184_complete_def",
  ``q2096184_complete
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) <=>
      !u : num -> 'a.
        q2096184_cauchy add neg norm u ==>
        ?ell : 'a. q2096184_tendsto add neg norm u ell``);

val q2096184_complex_hilbert_space_def = new_definition (
  "q2096184_complex_hilbert_space_def",
  ``q2096184_complex_hilbert_space
      (zero : 'h) (add : 'h -> 'h -> 'h) (neg : 'h -> 'h)
      (smul : complex -> 'h -> 'h)
      (inner : 'h -> 'h -> complex) (norm : 'h -> real) <=>
      q2096184_add_comm_group zero add neg /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!x. neg x = smul (-1) x) /\
      (!x y. inner x y = conj (inner y x)) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!a x y. inner (smul a x) y = conj a * inner x y) /\
      (!x. 0 <= RE (inner x x)) /\
      (!x. IM (inner x x) = 0) /\
      (!x. (inner x x = 0) <=> (x = zero)) /\
      (!x. norm x = sqrt (RE (inner x x))) /\
      q2096184_complete add neg norm``);

val q2096184_metric_open_def = new_definition (
  "q2096184_metric_open_def",
  ``q2096184_metric_open
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (s : 'v set) <=>
      !x.
        x IN s ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            norm (add y (neg x)) < epsilon ==> y IN s``);

val q2096184_volume_measure_def = new_definition (
  "q2096184_volume_measure_def",
  ``q2096184_volume_measure
      (m : 'v m_space)
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real) <=>
      measure_space m /\
      m_space m = UNIV /\
      measurable_sets m =
        sigma_sets UNIV {s | q2096184_metric_open add neg norm s} /\
      ?n basis.
        q2096184_orthonormal_basis zero add smul inner n basis /\
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

val q2096184_measurable_simple_def = new_definition (
  "q2096184_measurable_simple_def",
  ``q2096184_measurable_simple
      (m : 'v m_space) (s : 'v -> 'a) <=>
      FINITE (IMAGE s UNIV) /\
      !y : 'a. {x | s x = y} IN measurable_sets m``);

val q2096184_strongly_measurable_def = new_definition (
  "q2096184_strongly_measurable_def",
  ``q2096184_strongly_measurable
      (m : 'v m_space)
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (f : 'v -> 'a) <=>
      ?s : num -> 'v -> 'a.
        (!n. q2096184_measurable_simple m (s n)) /\
        !x. q2096184_tendsto add neg norm (\n. s n x) (f x)``);

val q2096184_bochner_integrable_def = new_definition (
  "q2096184_bochner_integrable_def",
  ``q2096184_bochner_integrable
      (m : 'v m_space)
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (f : 'v -> 'a) <=>
      ?g : 'v -> 'a.
        q2096184_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x)``);

val q2096184_simple_integral_def = new_definition (
  "q2096184_simple_integral_def",
  ``q2096184_simple_integral
      (m : 'v m_space)
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (smul : complex -> 'a -> 'a) (s : 'v -> 'a) =
      ITSET
        (\y acc.
          add
            (smul
              (complex_of_real (real (measure m {x | s x = y}))) y)
            acc)
        (IMAGE s UNIV DELETE zero) zero``);

val q2096184_bochner_approximates_def = new_definition (
  "q2096184_bochner_approximates_def",
  ``q2096184_bochner_approximates
      (m : 'v m_space)
      (zero : 'a) (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (smul : complex -> 'a -> 'a) (norm : 'a -> real)
      (f : 'v -> 'a) (s : num -> 'v -> 'a) (ell : 'a) <=>
      ?g : 'v -> 'a.
        q2096184_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x) /\
        (!n. q2096184_measurable_simple m (s n)) /\
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
        q2096184_tendsto add neg norm
          (\n. q2096184_simple_integral m zero add smul (s n))
          ell``);

val q2096184_bochner_integral_def = new_definition (
  "q2096184_bochner_integral_def",
  ``q2096184_bochner_integral
      (m : 'v m_space)
      (zero : 'a) (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (smul : complex -> 'a -> 'a) (norm : 'a -> real)
      (f : 'v -> 'a) =
      if q2096184_complete add neg norm /\
         q2096184_bochner_integrable m add neg norm f
      then
        @ell : 'a.
          ?s : num -> 'v -> 'a.
            q2096184_bochner_approximates
              m zero add neg smul norm f s ell
      else
        zero``);

val q2096184_has_coordinate_derivatives_def = new_definition (
  "q2096184_has_coordinate_derivatives_def",
  ``q2096184_has_coordinate_derivatives
      (addV : 'v -> 'v -> 'v) (smulV : real -> 'v -> 'v)
      (basis : num -> 'v) (n : num)
      (addH : 'h -> 'h -> 'h) (negH : 'h -> 'h)
      (smulH : complex -> 'h -> 'h) (normH : 'h -> real)
      (f : 'v -> 'h) (D : num list -> 'v -> 'h) <=>
      D [] = f /\
      !is j x.
        EVERY (\k. k < n) is /\ j < n ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !t : real.
              0 < abs t /\ abs t < delta ==>
              normH
                (addH
                  (smulH (complex_of_real (inv t))
                    (addH
                      (D is (addV x (smulV t (basis j))))
                      (negH (D is x))))
                  (negH (D (j::is) x))) <
              epsilon``);

val q2096184_continuous_def = new_definition (
  "q2096184_continuous_def",
  ``q2096184_continuous
      (addV : 'v -> 'v -> 'v) (smulV : real -> 'v -> 'v)
      (normV : 'v -> real)
      (addH : 'h -> 'h -> 'h) (negH : 'h -> 'h)
      (normH : 'h -> real) (h : 'v -> 'h) <=>
      !x epsilon.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y.
            normV (addV y (smulV (-1) x)) < delta ==>
            normH (addH (h y) (negH (h x))) < epsilon``);

val q2096184_schwartz_def = new_definition (
  "q2096184_schwartz_def",
  ``q2096184_schwartz
      (zeroV : 'v) (addV : 'v -> 'v -> 'v)
      (smulV : real -> 'v -> 'v) (innerV : 'v -> 'v -> real)
      (normV : 'v -> real)
      (addH : 'h -> 'h -> 'h) (negH : 'h -> 'h)
      (smulH : complex -> 'h -> 'h) (normH : 'h -> real)
      (f : 'v -> 'h) <=>
      ?n basis D.
        q2096184_orthonormal_basis
          zeroV addV smulV innerV n basis /\
        q2096184_has_coordinate_derivatives
          addV smulV basis n addH negH smulH normH f D /\
        (!is.
          EVERY (\k. k < n) is ==>
          q2096184_continuous
            addV smulV normV addH negH normH (D is)) /\
        !p is.
          EVERY (\k. k < n) is ==>
          ?C : real.
            0 <= C /\
            !x.
              (1 + normV x) pow p * normH (D is x) <= C``);

val q2096184_fourier_def = new_definition (
  "q2096184_fourier_def",
  ``q2096184_fourier
      (m : 'v m_space) (innerV : 'v -> 'v -> real)
      (zeroH : 'h) (addH : 'h -> 'h -> 'h) (negH : 'h -> 'h)
      (smulH : complex -> 'h -> 'h) (normH : 'h -> real)
      (f : 'v -> 'h) (xi : 'v) =
      q2096184_bochner_integral
        m zeroH addH negH smulH normH
        (\x.
          smulH
            (complex_exp
              (-(i * complex_of_real (2 * pi * innerV x xi))))
            (f x))``);

val q2096184_complex_integral_def = new_definition (
  "q2096184_complex_integral_def",
  ``q2096184_complex_integral
      (m : 'v m_space) (f : 'v -> complex) =
      q2096184_bochner_integral
        m 0 (\x y. x + y) (\x. -x) (\a x. a * x) modu f``);

val integral_inner_fourier_fourier =
  ``!(m : 'v m_space)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : real -> 'v -> 'v) (innerV : 'v -> 'v -> real)
      (normV : 'v -> real)
      (zeroH : 'h) (addH : 'h -> 'h -> 'h) (negH : 'h -> 'h)
      (smulH : complex -> 'h -> 'h)
      (innerH : 'h -> 'h -> complex) (normH : 'h -> real)
      (f : 'v -> 'h) (g : 'v -> 'h).
      q2096184_real_inner_product_space
        zeroV addV negV smulV innerV normV /\
      q2096184_volume_measure
        m zeroV addV negV smulV innerV normV /\
      q2096184_complex_hilbert_space
        zeroH addH negH smulH innerH normH /\
      q2096184_schwartz
        zeroV addV smulV innerV normV
        addH negH smulH normH f /\
      q2096184_schwartz
        zeroV addV smulV innerV normV
        addH negH smulH normH g
      ==>
      q2096184_complex_integral m
        (\xi.
          innerH
            (q2096184_fourier
              m innerV zeroH addH negH smulH normH f xi)
            (q2096184_fourier
              m innerV zeroH addH negH smulH normH g xi)) =
      q2096184_complex_integral m (\x. innerH (f x) (g x))``;
