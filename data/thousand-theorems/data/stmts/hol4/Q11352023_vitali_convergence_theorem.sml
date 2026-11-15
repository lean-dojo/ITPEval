(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q11352023, "Vitali convergence theorem": for a finite exponent p at least
  one, Lp convergence is equivalent to convergence in measure together with
  uniform integrability and uniform tightness. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory extrealTheory;
open topologyTheory real_topologyTheory measureTheory borelTheory lebesgueTheory;

val q11352023_normed_add_comm_group_def = new_definition (
  "q11352023_normed_add_comm_group_def",
  ``q11352023_normed_add_comm_group
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (norm : 'g -> real) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. 0 <= norm x) /\
      (!x. norm x = 0 <=> x = zero) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q11352023_tendsto_zero_def = new_definition (
  "q11352023_tendsto_zero_def",
  ``q11352023_tendsto_zero (u : num -> extreal) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N. !n. N <= n ==> u n <= Normal epsilon``);

val q11352023_measurable_simple_def = new_definition (
  "q11352023_measurable_simple_def",
  ``q11352023_measurable_simple
      (m : 'a m_space) (s : 'a -> 'g) <=>
      FINITE (IMAGE s UNIV) /\
      !y : 'g. {x | s x = y} IN measurable_sets m``);

val q11352023_tendsto_in_norm_def = new_definition (
  "q11352023_tendsto_in_norm_def",
  ``q11352023_tendsto_in_norm
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (u : num -> 'g) (ell : 'g) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N. !n. N <= n ==>
          norm (add (u n) (neg ell)) < epsilon``);

val q11352023_strongly_measurable_def = new_definition (
  "q11352023_strongly_measurable_def",
  ``q11352023_strongly_measurable
      (m : 'a m_space)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : 'a -> 'g) <=>
      ?s : num -> 'a -> 'g.
        (!n. q11352023_measurable_simple m (s n)) /\
        !x. q11352023_tendsto_in_norm add neg norm (\n. s n x) (f x)``);

val q11352023_ae_strongly_measurable_def = new_definition (
  "q11352023_ae_strongly_measurable_def",
  ``q11352023_ae_strongly_measurable
      (m : 'a m_space)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : 'a -> 'g) <=>
      ?h : 'a -> 'g.
        q11352023_strongly_measurable m add neg norm h /\
        (AE x::m. f x = h x)``);

val q11352023_rpow_def = new_definition (
  "q11352023_rpow_def",
  ``q11352023_rpow (r : real) (p : real) =
      if r = 0 then 0 else r rpow p``);

val q11352023_lp_norm_def = new_definition (
  "q11352023_lp_norm_def",
  ``q11352023_lp_norm
      (m : 'a m_space) (norm : 'g -> real) (p : real)
      (f : 'a -> 'g) =
      let integral_p =
        pos_fn_integral m
          (\x. Normal (q11352023_rpow (norm (f x)) p))
      in
        if integral_p = PosInf then PosInf
        else if integral_p = 0 then Normal 0
        else Normal (q11352023_rpow (real integral_p) (inv p))``);

val q11352023_mem_lp_def = new_definition (
  "q11352023_mem_lp_def",
  ``q11352023_mem_lp
      (m : 'a m_space)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (p : real) (f : 'a -> 'g) <=>
      q11352023_ae_strongly_measurable m add neg norm f /\
      q11352023_lp_norm m norm p f <> PosInf``);

val q11352023_indicator_def = new_definition (
  "q11352023_indicator_def",
  ``q11352023_indicator
      (zero : 'g) (s : 'a set) (f : 'a -> 'g) (x : 'a) =
      if x IN s then f x else zero``);

val q11352023_outer_measure_def = new_definition (
  "q11352023_outer_measure_def",
  ``q11352023_outer_measure (m : 'a m_space) (s : 'a set) =
      inf
        {r : extreal |
          ?t : 'a set.
            s SUBSET t /\
            t IN measurable_sets m /\
            measure m t = r}``);

val q11352023_tendsto_in_measure_def = new_definition (
  "q11352023_tendsto_in_measure_def",
  ``q11352023_tendsto_in_measure
      (m : 'a m_space)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : num -> 'a -> 'g) (g : 'a -> 'g) <=>
      !epsilon : real.
        0 < epsilon ==>
        q11352023_tendsto_zero
          (\n.
            q11352023_outer_measure m
              {x |
                epsilon <=
                  norm (add (f n x) (neg (g x)))})``);

val q11352023_unif_integrable_def = new_definition (
  "q11352023_unif_integrable_def",
  ``q11352023_unif_integrable
      (m : 'a m_space) (zero : 'g) (norm : 'g -> real)
      (p : real) (f : num -> 'a -> 'g) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !i s.
            s IN measurable_sets m /\
            measure m s <= Normal delta
            ==>
            q11352023_lp_norm m norm p
              (q11352023_indicator zero s (f i)) <= Normal epsilon``);

val q11352023_unif_tight_def = new_definition (
  "q11352023_unif_tight_def",
  ``q11352023_unif_tight
      (m : 'a m_space) (zero : 'g) (norm : 'g -> real)
      (p : real) (f : num -> 'a -> 'g) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?s : 'a set.
          q11352023_outer_measure m s <> PosInf /\
          !i.
            q11352023_lp_norm m norm p
              (q11352023_indicator zero (UNIV DIFF s) (f i))
              <= Normal epsilon``);

val vitali_convergence_theorem =
  ``!(m : 'a m_space)
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (norm : 'g -> real) (p : real)
      (f : num -> 'a -> 'g) (g : 'a -> 'g).
      measure_space m /\
      m_space m = UNIV /\
      q11352023_normed_add_comm_group zero add neg norm /\
      1 <= p /\
      (!n. q11352023_mem_lp m add neg norm p (f n)) /\
      q11352023_mem_lp m add neg norm p g
      ==>
      (q11352023_tendsto_in_measure m add neg norm f g /\
       q11352023_unif_integrable m zero norm p f /\
       q11352023_unif_tight m zero norm p f
       <=>
       q11352023_tendsto_zero
         (\n.
           q11352023_lp_norm m norm p
             (\x. add (f n x) (neg (g x)))))``;
