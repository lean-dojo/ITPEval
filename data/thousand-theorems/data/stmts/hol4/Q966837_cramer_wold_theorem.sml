(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q966837 (thousand-theorems__hol4__Q966837), "Cramér–Wold theorem":
  convergence in distribution in a finite-dimensional real inner-product
  space is equivalent to convergence in distribution of every scalar
  inner-product projection. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory iterateTheory realTheory transcTheory;
open topologyTheory real_topologyTheory extrealTheory sigma_algebraTheory;
open measureTheory borelTheory lebesgueTheory probabilityTheory;

val q966837_add_comm_group_def = new_definition (
  "q966837_add_comm_group_def",
  ``q966837_add_comm_group
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero)``);

val q966837_finite_real_inner_product_space_def = new_definition (
  "q966837_finite_real_inner_product_space_def",
  ``q966837_finite_real_inner_product_space
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real) <=>
      q966837_add_comm_group zero add neg /\
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
      ?d : num.
        ?basis : num -> 'v.
          (!j k.
            j IN count d /\ k IN count d ==>
            inner (basis j) (basis k) =
              if j = k then 1 else 0) /\
          !x.
            x =
              ITSET
                (\k acc. add (smul (inner x (basis k)) (basis k)) acc)
                (count d) zero``);

val q966837_norm_topology_def = new_definition (
  "q966837_norm_topology_def",
  ``q966837_norm_topology
      (top : 'v topology)
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) <=>
      topspace top = UNIV /\
      !u. open_in top u <=>
        !x. x IN u ==>
          ?epsilon : real.
            0 < epsilon /\
            !y. norm (add y (neg x)) < epsilon ==> y IN u``);

val q966837_borel_space_def = new_definition (
  "q966837_borel_space_def",
  ``q966837_borel_space
      (top : 'v topology) (a : 'v algebra) <=>
      topspace top = UNIV /\
      a = general_borel top``);

val q966837_ae_measurable_def = new_definition (
  "q966837_ae_measurable_def",
  ``q966837_ae_measurable
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) <=>
      ?h.
        h IN measurable (m_space m,measurable_sets m) a /\
        almost_everywhere m (\x. f x = h x)``);

val q966837_measurable_rep_def = new_definition (
  "q966837_measurable_rep_def",
  ``q966837_measurable_rep
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) =
      @h.
        h IN measurable (m_space m,measurable_sets m) a /\
        almost_everywhere m (\x. f x = h x)``);

val q966837_law_def = new_definition (
  "q966837_law_def",
  ``q966837_law
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) =
      (space a,subsets a,distr m (q966837_measurable_rep m a f))``);

val q966837_real_integral_def = new_definition (
  "q966837_real_integral_def",
  ``q966837_real_integral
      (m : 'a m_space) (f : 'a -> real) =
      real (integral m (Normal o f))``);

val q966837_tendsto_real_def = new_definition (
  "q966837_tendsto_real_def",
  ``q966837_tendsto_real (u : num -> real) (ell : real) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num.
            N <= n ==> abs (u n - ell) < epsilon``);

val q966837_weak_tendsto_def = new_definition (
  "q966837_weak_tendsto_def",
  ``q966837_weak_tendsto
      (top : 'b topology)
      (nu : num -> 'b m_space) (nu0 : 'b m_space) <=>
      !f : 'b -> real.
        f IN bounded_continuous top ==>
        q966837_tendsto_real
          (\n. q966837_real_integral (nu n) f)
          (q966837_real_integral nu0 f)``);

val q966837_tendsto_in_distribution_def = new_definition (
  "q966837_tendsto_in_distribution_def",
  ``q966837_tendsto_in_distribution
      (top : 'b topology) (a : 'b algebra)
      (m : 'w m_space) (m' : 'w2 m_space)
      (X : num -> 'w -> 'b) (X' : 'w2 -> 'b) <=>
      (!n. q966837_ae_measurable m a (X n)) /\
      q966837_ae_measurable m' a X' /\
      q966837_weak_tendsto top
        (\n. q966837_law m a (X n))
        (q966837_law m' a X')``);

val cramer_wold_theorem =
  ``!(top : 'v topology) (a : 'v algebra)
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (inner : 'v -> 'v -> real)
      (norm : 'v -> real)
      (P : 'w m_space) (P' : 'w2 m_space)
      (X : num -> 'w -> 'v) (X' : 'w2 -> 'v).
      q966837_finite_real_inner_product_space
        zero add neg smul inner norm /\
      q966837_norm_topology top add neg norm /\
      q966837_borel_space top a /\
      prob_space P /\
      m_space P = UNIV /\
      prob_space P' /\
      m_space P' = UNIV /\
      q966837_ae_measurable P' a X' /\
      (!n. q966837_ae_measurable P a (X n))
      ==>
      (q966837_tendsto_in_distribution top a P P' X X' <=>
       !t : 'v.
         q966837_tendsto_in_distribution euclidean borel P P'
           (\n w. inner (X n w) t)
           (\w. inner (X' w) t))``;
