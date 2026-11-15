(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3526996, "Kolmogorov extension theorem": a projectively consistent family
  of finite measures on finite products of Polish Borel spaces has a measure
  on the full dependent product with exactly those marginals. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory optionTheory pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory;

val q3526996_metric_on_def = new_definition (
  "q3526996_metric_on_def",
  ``q3526996_metric_on
      (carrier : 'x set) (dist : 'x -> 'x -> real) <=>
      (!x y.
        x IN carrier /\ y IN carrier ==>
        0 <= dist x y /\
        (dist x y = 0 <=> x = y) /\
        dist x y = dist y x) /\
      (!x y z.
        x IN carrier /\ y IN carrier /\ z IN carrier ==>
        dist x z <= dist x y + dist y z)``);

val q3526996_open_def = new_definition (
  "q3526996_open_def",
  ``q3526996_open
      (carrier : 'x set) (dist : 'x -> 'x -> real) (s : 'x set) <=>
      s SUBSET carrier /\
      !x.
        x IN s ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            y IN carrier /\ dist x y < epsilon ==> y IN s``);

val q3526996_cauchy_def = new_definition (
  "q3526996_cauchy_def",
  ``q3526996_cauchy
      (carrier : 'x set) (dist : 'x -> 'x -> real)
      (u : num -> 'x) <=>
      (!n. u n IN carrier) /\
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !m n.
            N <= m /\ N <= n ==>
            dist (u m) (u n) < epsilon``);

val q3526996_tendsto_def = new_definition (
  "q3526996_tendsto_def",
  ``q3526996_tendsto
      (carrier : 'x set) (dist : 'x -> 'x -> real)
      (u : num -> 'x) (x : 'x) <=>
      x IN carrier /\
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n. N <= n ==> dist (u n) x < epsilon``);

val q3526996_complete_def = new_definition (
  "q3526996_complete_def",
  ``q3526996_complete
      (carrier : 'x set) (dist : 'x -> 'x -> real) <=>
      !u : num -> 'x.
        q3526996_cauchy carrier dist u ==>
        ?x. q3526996_tendsto carrier dist u x``);

val q3526996_separable_def = new_definition (
  "q3526996_separable_def",
  ``q3526996_separable
      (carrier : 'x set) (dist : 'x -> 'x -> real) <=>
      ?u : num -> 'x.
        !x epsilon.
          x IN carrier /\ 0 < epsilon ==>
          ?n. u n IN carrier /\ dist x (u n) < epsilon``);

val q3526996_polish_borel_space_def = new_definition (
  "q3526996_polish_borel_space_def",
  ``q3526996_polish_borel_space
      (a : 'x algebra) (dist : 'x -> 'x -> real) <=>
      sigma_algebra a /\
      q3526996_metric_on (space a) dist /\
      q3526996_complete (space a) dist /\
      q3526996_separable (space a) dist /\
      a =
        sigma
          (space a)
          {s : 'x set |
             q3526996_open (space a) dist s}``);

val q3526996_finite_product_carrier_def = new_definition (
  "q3526996_finite_product_carrier_def",
  ``q3526996_finite_product_carrier
      (spaces : 'i -> 'x algebra) (J : 'i set) =
      {p : ('i -> 'x option) |
         !i.
           if i IN J then
             ?x. p i = SOME x /\ x IN space (spaces i)
           else
             p i = NONE}``);

val q3526996_path_carrier_def = new_definition (
  "q3526996_path_carrier_def",
  ``q3526996_path_carrier (spaces : 'i -> 'x algebra) =
      {p : ('i -> 'x option) |
         !i. ?x. p i = SOME x /\ x IN space (spaces i)}``);

val q3526996_finite_product_space_def = new_definition (
  "q3526996_finite_product_space_def",
  ``q3526996_finite_product_space
      (spaces : 'i -> 'x algebra) (J : 'i set) =
      sigma
        (q3526996_finite_product_carrier spaces J)
        {c : ('i -> 'x option) set |
           ?i s.
             i IN J /\
             s IN subsets (spaces i) /\
             c =
               {p |
                  p IN q3526996_finite_product_carrier spaces J /\
                  ?x. p i = SOME x /\ x IN s}}``);

val q3526996_path_space_def = new_definition (
  "q3526996_path_space_def",
  ``q3526996_path_space (spaces : 'i -> 'x algebra) =
      sigma
        (q3526996_path_carrier spaces)
        {c : ('i -> 'x option) set |
           ?i s.
             s IN subsets (spaces i) /\
             c =
               {p |
                  p IN q3526996_path_carrier spaces /\
                  ?x. p i = SOME x /\ x IN s}}``);

val q3526996_restrict_def = new_definition (
  "q3526996_restrict_def",
  ``q3526996_restrict
      (J : 'i set) (p : 'i -> 'x option) =
      \i. if i IN J then p i else NONE``);

val q3526996_projective_measure_family_def = new_definition (
  "q3526996_projective_measure_family_def",
  ``q3526996_projective_measure_family
      (spaces : 'i -> 'x algebra)
      (P : 'i set -> ('i -> 'x option) m_space) <=>
      (!J.
        FINITE J ==>
        measure_space (P J) /\
        m_space (P J) =
          q3526996_finite_product_carrier spaces J /\
        measurable_sets (P J) =
          subsets (q3526996_finite_product_space spaces J) /\
        ~(measure (P J) (m_space (P J)) = PosInf)) /\
      (!J K.
        FINITE J /\ FINITE K /\ J SUBSET K ==>
        !s.
          s IN subsets (q3526996_finite_product_space spaces J) ==>
          measure
            (P K)
            {p |
               p IN q3526996_finite_product_carrier spaces K /\
               q3526996_restrict J p IN s} =
          measure (P J) s)``);

val q3526996_is_projective_limit_def = new_definition (
  "q3526996_is_projective_limit_def",
  ``q3526996_is_projective_limit
      (spaces : 'i -> 'x algebra)
      (P : 'i set -> ('i -> 'x option) m_space)
      (mu : ('i -> 'x option) m_space) <=>
      measure_space mu /\
      m_space mu = q3526996_path_carrier spaces /\
      measurable_sets mu = subsets (q3526996_path_space spaces) /\
      !J s.
        FINITE J /\
        s IN subsets (q3526996_finite_product_space spaces J)
        ==>
        measure
          mu
          {p |
             p IN q3526996_path_carrier spaces /\
             q3526996_restrict J p IN s} =
        measure (P J) s``);

val q3526996_projective_limit_def = new_definition (
  "q3526996_projective_limit_def",
  ``q3526996_projective_limit
      (spaces : 'i -> 'x algebra)
      (P : 'i set -> ('i -> 'x option) m_space) =
      @mu : ('i -> 'x option) m_space.
        q3526996_is_projective_limit spaces P mu``);

val kolmogorov_extension_theorem =
  ``!(spaces : 'i -> 'x algebra)
      (dist : 'i -> 'x -> 'x -> real)
      (P : 'i set -> ('i -> 'x option) m_space).
      (!i. q3526996_polish_borel_space (spaces i) (dist i)) /\
      q3526996_projective_measure_family spaces P
      ==>
      q3526996_is_projective_limit
        spaces P (q3526996_projective_limit spaces P)``;
