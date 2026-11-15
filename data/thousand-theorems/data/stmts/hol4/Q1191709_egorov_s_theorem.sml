(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1191709 (thousand-theorems__hol4__Q1191709), "Egorov's theorem":
  almost-everywhere convergence of strongly measurable functions on a
  measurable set of finite measure is uniform outside a measurable subset
  of arbitrarily small measure. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open measureTheory;

val q1191709_semilattice_sup_def = new_definition (
  "q1191709_semilattice_sup_def",
  ``q1191709_semilattice_sup
      (leq : 'i -> 'i -> bool) (join : 'i -> 'i -> 'i) <=>
      (!x. leq x x) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x (join x y)) /\
      (!x y. leq y (join x y)) /\
      (!x y z. leq x z /\ leq y z ==> leq (join x y) z)``);

val q1191709_countable_def = new_definition (
  "q1191709_countable_def",
  ``q1191709_countable (carrier : 'i set) <=>
      ?encode : 'i -> num.
        INJ encode carrier (UNIV : num set)``);

val q1191709_pseudo_emetric_def = new_definition (
  "q1191709_pseudo_emetric_def",
  ``q1191709_pseudo_emetric (edist : 'b -> 'b -> extreal) <=>
      (!x. edist x x = 0) /\
      (!x y. 0 <= edist x y) /\
      (!x y. edist x y = edist y x) /\
      (!x y z. edist x z <= edist x y + edist y z)``);

val q1191709_tendsto_sequence_def = new_definition (
  "q1191709_tendsto_sequence_def",
  ``q1191709_tendsto_sequence
      (edist : 'b -> 'b -> extreal)
      (u : num -> 'b) (ell : 'b) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N. !n. N <= n ==> edist (u n) ell < Normal epsilon``);

val q1191709_measurable_simple_def = new_definition (
  "q1191709_measurable_simple_def",
  ``q1191709_measurable_simple
      (m : 'a m_space) (u : 'a -> 'b) <=>
      FINITE (IMAGE u UNIV) /\
      !y : 'b. {x | u x = y} IN measurable_sets m``);

val q1191709_strongly_measurable_def = new_definition (
  "q1191709_strongly_measurable_def",
  ``q1191709_strongly_measurable
      (m : 'a m_space) (edist : 'b -> 'b -> extreal)
      (h : 'a -> 'b) <=>
      ?u : num -> 'a -> 'b.
        (!n. q1191709_measurable_simple m (u n)) /\
        !x. q1191709_tendsto_sequence edist (\n. u n x) (h x)``);

val q1191709_tendsto_at_top_def = new_definition (
  "q1191709_tendsto_at_top_def",
  ``q1191709_tendsto_at_top
      (leq : 'i -> 'i -> bool) (edist : 'b -> 'b -> extreal)
      (u : 'i -> 'b) (ell : 'b) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?i0. !i. leq i0 i ==> edist (u i) ell < Normal epsilon``);

val q1191709_tendsto_uniformly_on_def = new_definition (
  "q1191709_tendsto_uniformly_on_def",
  ``q1191709_tendsto_uniformly_on
      (leq : 'i -> 'i -> bool) (edist : 'b -> 'b -> extreal)
      (f : 'i -> 'a -> 'b) (g : 'a -> 'b) (u : 'a set) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?i0. !i x.
          leq i0 i /\ x IN u ==>
          edist (f i x) (g x) < Normal epsilon``);

val tendstoUniformlyOn_of_ae_tendsto =
  ``!(m : 'a m_space)
      (leq : 'i -> 'i -> bool) (join : 'i -> 'i -> 'i)
      (edist : 'b -> 'b -> extreal)
      (f : 'i -> 'a -> 'b) (g : 'a -> 'b)
      (s : 'a set) (epsilon : real).
      measure_space m /\
      m_space m = UNIV /\
      q1191709_semilattice_sup leq join /\
      q1191709_countable (UNIV : 'i set) /\
      q1191709_pseudo_emetric edist /\
      (!i. q1191709_strongly_measurable m edist (f i)) /\
      q1191709_strongly_measurable m edist g /\
      s IN measurable_sets m /\
      measure m s <> PosInf /\
      (AE x::m.
        x IN s ==>
        q1191709_tendsto_at_top leq edist (\i. f i x) (g x)) /\
      0 < epsilon
      ==>
      ?t : 'a set.
        t SUBSET s /\
        t IN measurable_sets m /\
        measure m t <= Normal epsilon /\
        q1191709_tendsto_uniformly_on
          leq edist f g (s DIFF t)``;
