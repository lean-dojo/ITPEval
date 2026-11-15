(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1149022, "Fubini's theorem": the Bochner integral of an integrable
  function on the product of two s-finite measure spaces equals its iterated
  Bochner integral. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory measureTheory borelTheory lebesgueTheory;
open martingaleTheory;

val q1149022_real_normed_space_def = new_definition (
  "q1149022_real_normed_space_def",
  ``q1149022_real_normed_space
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real) <=>
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

val q1149022_tendsto_def = new_definition (
  "q1149022_tendsto_def",
  ``q1149022_tendsto
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (u : num -> 'g) (ell : 'g) <=>
      !epsilon.
        0 < epsilon ==>
        ?N. !n. N <= n ==> norm (add (u n) (neg ell)) < epsilon``);

val q1149022_cauchy_def = new_definition (
  "q1149022_cauchy_def",
  ``q1149022_cauchy
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (u : num -> 'g) <=>
      !epsilon.
        0 < epsilon ==>
        ?N. !p q. N <= p /\ N <= q ==>
          norm (add (u p) (neg (u q))) < epsilon``);

val q1149022_complete_def = new_definition (
  "q1149022_complete_def",
  ``q1149022_complete
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real) <=>
      !u : num -> 'g.
        q1149022_cauchy add neg norm u ==>
        ?ell. q1149022_tendsto add neg norm u ell``);

val q1149022_sfinite_def = new_definition (
  "q1149022_sfinite_def",
  ``q1149022_sfinite (m : 'a m_space) <=>
      ?parts : num -> 'a set -> extreal.
        (!n.
          measure_space (m_space m,measurable_sets m,parts n) /\
          parts n (m_space m) <> PosInf) /\
        !s.
          s IN measurable_sets m ==>
          measure m s = suminf (\n. parts n s)``);

val q1149022_measurable_simple_def = new_definition (
  "q1149022_measurable_simple_def",
  ``q1149022_measurable_simple
      (m : 'a m_space) (s : 'a -> 'g) <=>
      FINITE (IMAGE s UNIV) /\
      !y : 'g. {x | s x = y} IN measurable_sets m``);

val q1149022_strongly_measurable_def = new_definition (
  "q1149022_strongly_measurable_def",
  ``q1149022_strongly_measurable
      (m : 'a m_space)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : 'a -> 'g) <=>
      ?s : num -> 'a -> 'g.
        (!n. q1149022_measurable_simple m (s n)) /\
        !x. q1149022_tendsto add neg norm (\n. s n x) (f x)``);

val q1149022_ae_strongly_measurable_def = new_definition (
  "q1149022_ae_strongly_measurable_def",
  ``q1149022_ae_strongly_measurable
      (m : 'a m_space)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : 'a -> 'g) <=>
      ?g : 'a -> 'g.
        q1149022_strongly_measurable m add neg norm g /\
        (AE x::m. f x = g x)``);

val q1149022_bochner_integrable_def = new_definition (
  "q1149022_bochner_integrable_def",
  ``q1149022_bochner_integrable
      (m : 'a m_space)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : 'a -> 'g) <=>
      ?g : 'a -> 'g.
        q1149022_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x)``);

val q1149022_simple_integral_def = new_definition (
  "q1149022_simple_integral_def",
  ``q1149022_simple_integral
      (m : 'a m_space) (zero : 'g) (add : 'g -> 'g -> 'g)
      (smul : real -> 'g -> 'g) (s : 'a -> 'g) =
      ITSET
        (\y acc.
          add (smul (real (measure m {x | s x = y})) y) acc)
        (IMAGE s UNIV DELETE zero) zero``);

val q1149022_bochner_approximates_def = new_definition (
  "q1149022_bochner_approximates_def",
  ``q1149022_bochner_approximates
      (m : 'a m_space) (zero : 'g) (add : 'g -> 'g -> 'g)
      (neg : 'g -> 'g) (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (f : 'a -> 'g) (s : num -> 'a -> 'g) (ell : 'g) <=>
      ?g : 'a -> 'g.
        q1149022_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x) /\
        (!n. q1149022_measurable_simple m (s n)) /\
        (!n. integrable m (Normal o (\x. norm (s n x)))) /\
        (!n.
          integrable m
            (Normal o (\x. norm (add (s n x) (neg (g x)))))) /\
        (((\n.
            real
              (integral m
                (Normal o (\x. norm (add (s n x) (neg (g x))))))) -->
          0) sequentially) /\
        q1149022_tendsto add neg norm
          (\n. q1149022_simple_integral m zero add smul (s n))
          ell``);

val q1149022_bochner_integral_def = new_definition (
  "q1149022_bochner_integral_def",
  ``q1149022_bochner_integral
      (m : 'a m_space) (zero : 'g) (add : 'g -> 'g -> 'g)
      (neg : 'g -> 'g) (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (f : 'a -> 'g) =
      if q1149022_complete add neg norm /\
         q1149022_bochner_integrable m add neg norm f
      then
        @ell.
          ?s : num -> 'a -> 'g.
            q1149022_bochner_approximates
              m zero add neg smul norm f s ell
      else
        zero``);

val integral_prod =
  ``!(m1 : 'a m_space) (m2 : 'b m_space)
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (f : ('a # 'b) -> 'g).
      measure_space m1 /\
      measure_space m2 /\
      m_space m1 = UNIV /\
      m_space m2 = UNIV /\
      q1149022_sfinite m1 /\
      q1149022_sfinite m2 /\
      q1149022_real_normed_space zero add neg smul norm /\
      q1149022_bochner_integrable
        (prod_measure_space m1 m2) add neg norm f
      ==>
      q1149022_bochner_integral
        (prod_measure_space m1 m2) zero add neg smul norm f =
      q1149022_bochner_integral
        m1 zero add neg smul norm
        (\x.
          q1149022_bochner_integral
            m2 zero add neg smul norm (\y. f (x,y)))``;
