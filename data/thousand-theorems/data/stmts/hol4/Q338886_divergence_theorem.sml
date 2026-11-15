(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q338886, "Divergence theorem": on a box in an arbitrary nonempty finite
  dimensional real coordinate space, the Bochner integral of the divergence
  of a continuous vector field differentiable off a countable set equals the
  signed sum of its integrals over opposite faces. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory sigma_algebraTheory;
open measureTheory borelTheory lebesgueTheory;

val q338886_real_max_def = new_definition (
  "q338886_real_max_def",
  ``q338886_real_max (x : real) (y : real) =
      if x <= y then y else x``);

val q338886_sup_norm_def = new_definition (
  "q338886_sup_norm_def",
  ``q338886_sup_norm
      (norm : 'a -> real) (v : 'i -> 'a) =
      ITSET q338886_real_max (IMAGE (\i. norm (v i)) UNIV) 0``);

val q338886_vec_dist_def = new_definition (
  "q338886_vec_dist_def",
  ``q338886_vec_dist (x : 'i -> real) (y : 'i -> real) =
      q338886_sup_norm abs (\i. x i - y i)``);

val q338886_real_normed_space_def = new_definition (
  "q338886_real_normed_space_def",
  ``q338886_real_normed_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. 0 <= norm x) /\
      (!x. norm x = 0 <=> x = zero) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = abs a * norm x)``);

val q338886_tendsto_def = new_definition (
  "q338886_tendsto_def",
  ``q338886_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (u : num -> 'e) (ell : 'e) <=>
      !epsilon.
        0 < epsilon ==>
        ?N. !n. N <= n ==> norm (add (u n) (neg ell)) < epsilon``);

val q338886_cauchy_def = new_definition (
  "q338886_cauchy_def",
  ``q338886_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (u : num -> 'e) <=>
      !epsilon.
        0 < epsilon ==>
        ?N. !p q. N <= p /\ N <= q ==>
          norm (add (u p) (neg (u q))) < epsilon``);

val q338886_complete_def = new_definition (
  "q338886_complete_def",
  ``q338886_complete
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real) <=>
      !u : num -> 'e.
        q338886_cauchy add neg norm u ==>
        ?ell. q338886_tendsto add neg norm u ell``);

val q338886_open_def = new_definition (
  "q338886_open_def",
  ``q338886_open (u : ('i -> real) set) <=>
      !x. x IN u ==>
        ?epsilon.
          0 < epsilon /\
          !y. q338886_vec_dist y x < epsilon ==> y IN u``);

val q338886_borel_measure_def = new_definition (
  "q338886_borel_measure_def",
  ``q338886_borel_measure (m : ('i -> real) m_space) <=>
      measure_space m /\
      m_space m = UNIV /\
      measurable_sets m =
        subsets
          (sigma UNIV
            {u : ('i -> real) set | q338886_open u})``);

val q338886_nonnegative_product_def = new_definition (
  "q338886_nonnegative_product_def",
  ``q338886_nonnegative_product
      (indices : 'i set) (a : 'i -> real) (b : 'i -> real) =
      ITSET
        (\i acc. q338886_real_max (b i - a i) 0 * acc)
        indices 1``);

val q338886_Ioc_box_def = new_definition (
  "q338886_Ioc_box_def",
  ``q338886_Ioc_box
      (a : 'i -> real) (b : 'i -> real) =
      {x | !i. a i < x i /\ x i <= b i}``);

val q338886_face_Ioc_box_def = new_definition (
  "q338886_face_Ioc_box_def",
  ``q338886_face_Ioc_box
      (i : 'i) (a : 'i -> real) (b : 'i -> real) =
      {x |
        x i = 0 /\
        !j. j <> i ==> a j < x j /\ x j <= b j}``);

val q338886_volume_measure_def = new_definition (
  "q338886_volume_measure_def",
  ``q338886_volume_measure (m : ('i -> real) m_space) <=>
      q338886_borel_measure m /\
      !a b : 'i -> real.
        measure m (q338886_Ioc_box a b) =
        Normal (q338886_nonnegative_product UNIV a b)``);

val q338886_face_volume_measure_def = new_definition (
  "q338886_face_volume_measure_def",
  ``q338886_face_volume_measure
      (i : 'i) (m : ('i -> real) m_space) <=>
      q338886_borel_measure m /\
      !a b : 'i -> real.
        measure m (q338886_face_Ioc_box i a b) =
        Normal
          (q338886_nonnegative_product (UNIV DELETE i) a b)``);

val q338886_volume_def = new_definition (
  "q338886_volume_def",
  ``q338886_volume : ('i -> real) m_space =
      @m. q338886_volume_measure m``);

val q338886_face_volume_def = new_definition (
  "q338886_face_volume_def",
  ``q338886_face_volume (i : 'i) : ('i -> real) m_space =
      @m. q338886_face_volume_measure i m``);

val q338886_measurable_simple_def = new_definition (
  "q338886_measurable_simple_def",
  ``q338886_measurable_simple
      (m : 'a m_space) (s : 'a -> 'e) <=>
      FINITE (IMAGE s UNIV) /\
      !y : 'e. {x | s x = y} IN measurable_sets m``);

val q338886_strongly_measurable_def = new_definition (
  "q338886_strongly_measurable_def",
  ``q338886_strongly_measurable
      (m : 'a m_space)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (f : 'a -> 'e) <=>
      ?s : num -> 'a -> 'e.
        (!n. q338886_measurable_simple m (s n)) /\
        !x. q338886_tendsto add neg norm (\n. s n x) (f x)``);

val q338886_bochner_integrable_def = new_definition (
  "q338886_bochner_integrable_def",
  ``q338886_bochner_integrable
      (m : 'a m_space)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (f : 'a -> 'e) <=>
      ?g : 'a -> 'e.
        q338886_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x)``);

val q338886_simple_integral_def = new_definition (
  "q338886_simple_integral_def",
  ``q338886_simple_integral
      (m : 'a m_space) (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : real -> 'e -> 'e) (s : 'a -> 'e) =
      ITSET
        (\y acc.
          add (smul (real (measure m {x | s x = y})) y) acc)
        (IMAGE s UNIV DELETE zero) zero``);

val q338886_bochner_approximates_def = new_definition (
  "q338886_bochner_approximates_def",
  ``q338886_bochner_approximates
      (m : 'a m_space) (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (f : 'a -> 'e) (s : num -> 'a -> 'e) (ell : 'e) <=>
      ?g : 'a -> 'e.
        q338886_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x) /\
        (!n. q338886_measurable_simple m (s n)) /\
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
        q338886_tendsto add neg norm
          (\n. q338886_simple_integral m zero add smul (s n))
          ell``);

val q338886_bochner_integral_def = new_definition (
  "q338886_bochner_integral_def",
  ``q338886_bochner_integral
      (m : 'a m_space) (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (f : 'a -> 'e) =
      if q338886_complete add neg norm /\
         q338886_bochner_integrable m add neg norm f
      then
        @ell.
          ?s : num -> 'a -> 'e.
            q338886_bochner_approximates
              m zero add neg smul norm f s ell
      else
        zero``);

val q338886_integrable_on_def = new_definition (
  "q338886_integrable_on_def",
  ``q338886_integrable_on
      (m : 'a m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (norm : 'e -> real)
      (s : 'a set) (f : 'a -> 'e) <=>
      q338886_bochner_integrable m add neg norm
        (\x. if x IN s then f x else zero)``);

val q338886_set_integral_def = new_definition (
  "q338886_set_integral_def",
  ``q338886_set_integral
      (m : 'a m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (s : 'a set) (f : 'a -> 'e) =
      q338886_bochner_integral m zero add neg smul norm
        (\x. if x IN s then f x else zero)``);

val q338886_closed_box_def = new_definition (
  "q338886_closed_box_def",
  ``q338886_closed_box
      (a : 'i -> real) (b : 'i -> real) =
      {x | !i. a i <= x i /\ x i <= b i}``);

val q338886_open_box_def = new_definition (
  "q338886_open_box_def",
  ``q338886_open_box
      (a : 'i -> real) (b : 'i -> real) =
      {x | !i. a i < x i /\ x i < b i}``);

val q338886_face_box_def = new_definition (
  "q338886_face_box_def",
  ``q338886_face_box
      (i : 'i) (a : 'i -> real) (b : 'i -> real) =
      {x |
        x i = 0 /\
        !j. j <> i ==> a j <= x j /\ x j <= b j}``);

val q338886_replace_def = new_definition (
  "q338886_replace_def",
  ``q338886_replace
      (x : 'i -> real) (i : 'i) (c : real) =
      \j. if j = i then c else x j``);

val q338886_basis_def = new_definition (
  "q338886_basis_def",
  ``q338886_basis (i : 'i) =
      \j. if j = i then 1 else 0``);

val q338886_continuous_on_def = new_definition (
  "q338886_continuous_on_def",
  ``q338886_continuous_on
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (f : ('i -> real) -> 'i -> 'e) (s : ('i -> real) set) <=>
      !x.
        x IN s ==>
        !epsilon.
          0 < epsilon ==>
          ?delta.
            0 < delta /\
            !y.
              y IN s /\ q338886_vec_dist y x < delta ==>
              q338886_sup_norm norm
                (\i. add (f y i) (neg (f x i))) < epsilon``);

val q338886_continuous_linear_map_def = new_definition (
  "q338886_continuous_linear_map_def",
  ``q338886_continuous_linear_map
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (L : ('i -> real) -> 'i -> 'e) <=>
      (!u v i.
        L (\j. u j + v j) i = add (L u i) (L v i)) /\
      (!c u i.
        L (\j. c * u j) i = smul c (L u i)) /\
      (?C.
        0 <= C /\
        !u.
          q338886_sup_norm norm (L u) <=
          C * q338886_sup_norm abs u)``);

val q338886_has_fderiv_at_def = new_definition (
  "q338886_has_fderiv_at_def",
  ``q338886_has_fderiv_at
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (f : ('i -> real) -> 'i -> 'e)
      (L : ('i -> real) -> 'i -> 'e) (x : 'i -> real) <=>
      q338886_continuous_linear_map zero add smul norm L /\
      !epsilon.
        0 < epsilon ==>
        ?delta.
          0 < delta /\
          !y.
            0 < q338886_vec_dist y x /\
            q338886_vec_dist y x < delta ==>
            q338886_sup_norm norm
              (\i.
                add
                  (add (f y i) (neg (f x i)))
                  (neg (L (\j. y j - x j) i))) <
            epsilon * q338886_vec_dist y x``);

val q338886_countable_def = new_definition (
  "q338886_countable_def",
  ``q338886_countable (s : ('i -> real) set) <=>
      ?encode : ('i -> real) -> num.
        INJ encode s (UNIV : num set)``);

val q338886_finite_sum_def = new_definition (
  "q338886_finite_sum_def",
  ``q338886_finite_sum
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (indices : 'i set) (g : 'i -> 'e) =
      ITSET (\i acc. add (g i) acc) indices zero``);

val integral_divergence_of_hasFDerivAt_off_countable =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (a : 'i -> real) (b : 'i -> real)
      (f : ('i -> real) -> 'i -> 'e)
      (f' : ('i -> real) -> ('i -> real) -> 'i -> 'e)
      (s : ('i -> real) set).
      FINITE (UNIV : 'i set) /\
      UNIV <> ({} : 'i set) /\
      q338886_real_normed_space zero add neg smul norm /\
      q338886_volume_measure (q338886_volume : ('i -> real) m_space) /\
      (!i : 'i.
        q338886_face_volume_measure i
          (q338886_face_volume i : ('i -> real) m_space)) /\
      (!i. a i <= b i) /\
      q338886_countable s /\
      (!x.
        q338886_continuous_linear_map zero add smul norm (f' x)) /\
      q338886_continuous_on add neg norm f
        (q338886_closed_box a b) /\
      (!x.
        x IN q338886_open_box a b /\ ~(x IN s) ==>
        q338886_has_fderiv_at zero add neg smul norm f (f' x) x) /\
      q338886_integrable_on
        (q338886_volume : ('i -> real) m_space)
        zero add neg norm (q338886_closed_box a b)
        (\x.
          q338886_finite_sum zero add UNIV
            (\i. f' x (q338886_basis i) i))
      ==>
      q338886_set_integral
        (q338886_volume : ('i -> real) m_space)
        zero add neg smul norm (q338886_closed_box a b)
        (\x.
          q338886_finite_sum zero add UNIV
            (\i. f' x (q338886_basis i) i)) =
      q338886_finite_sum zero add UNIV
        (\i.
          add
            (q338886_set_integral
              (q338886_face_volume i : ('i -> real) m_space)
              zero add neg smul norm (q338886_face_box i a b)
              (\x. f (q338886_replace x i (b i)) i))
            (neg
              (q338886_set_integral
                (q338886_face_volume i : ('i -> real) m_space)
                zero add neg smul norm (q338886_face_box i a b)
                (\x. f (q338886_replace x i (a i)) i))))``;
