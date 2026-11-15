(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3229352, "Vitali covering theorem": a fine family of closed sets satisfying
  a uniform enlarged-ball measure bound has a countable pairwise-disjoint
  subfamily covering the given set up to a null remainder. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory cardinalTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory;

val q3229352_pseudo_metric_def = new_definition (
  "q3229352_pseudo_metric_def",
  ``q3229352_pseudo_metric (d : 'a -> 'a -> real) <=>
      (!x. d x x = 0) /\
      (!x y. 0 <= d x y) /\
      (!x y. d x y = d y x) /\
      (!x y z. d x z <= d x y + d y z)``);

val q3229352_closed_ball_def = new_definition (
  "q3229352_closed_ball_def",
  ``q3229352_closed_ball
      (d : 'a -> 'a -> real) (x : 'a) (radius : real) =
      {y | d y x <= radius}``);

val q3229352_open_def = new_definition (
  "q3229352_open_def",
  ``q3229352_open (d : 'a -> 'a -> real) (u : 'a set) <=>
      !x.
        x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. d y x < epsilon ==> y IN u``);

val q3229352_closed_def = new_definition (
  "q3229352_closed_def",
  ``q3229352_closed (d : 'a -> 'a -> real) (s : 'a set) <=>
      q3229352_open d (UNIV DIFF s)``);

val q3229352_second_countable_def = new_definition (
  "q3229352_second_countable_def",
  ``q3229352_second_countable (d : 'a -> 'a -> real) <=>
      ?basis : ('a set) set.
        COUNTABLE basis /\
        (!v. v IN basis ==> q3229352_open d v) /\
        !u x.
          q3229352_open d u /\ x IN u ==>
          ?v.
            v IN basis /\
            x IN v /\
            v SUBSET u``);

val q3229352_opens_measurable_def = new_definition (
  "q3229352_opens_measurable_def",
  ``q3229352_opens_measurable
      (m : 'a m_space) (d : 'a -> 'a -> real) <=>
      !u.
        q3229352_open d u ==>
        u IN measurable_sets m``);

val q3229352_outer_measure_def = new_definition (
  "q3229352_outer_measure_def",
  ``q3229352_outer_measure (m : 'a m_space) (s : 'a set) =
      inf
        {value : extreal |
          ?measurable_superset : 'a set.
            s SUBSET measurable_superset /\
            measurable_superset IN measurable_sets m /\
            measure m measurable_superset = value}``);

val q3229352_locally_finite_def = new_definition (
  "q3229352_locally_finite_def",
  ``q3229352_locally_finite
      (m : 'a m_space) (d : 'a -> 'a -> real) <=>
      !x.
        ?u : 'a set.
          q3229352_open d u /\
          x IN u /\
          measure m u <> PosInf``);

val q3229352_nonempty_interior_def = new_definition (
  "q3229352_nonempty_interior_def",
  ``q3229352_nonempty_interior
      (d : 'a -> 'a -> real) (s : 'a set) <=>
      ?u x.
        q3229352_open d u /\
        x IN u /\
        u SUBSET s``);

val q3229352_pairwise_disjoint_def = new_definition (
  "q3229352_pairwise_disjoint_def",
  ``q3229352_pairwise_disjoint
      (u : 'i set) (B : 'i -> 'a set) <=>
      !a b.
        a IN u /\ b IN u /\ a <> b ==>
        DISJOINT (B a) (B b)``);

val exists_disjoint_covering_ae =
  ``!(m : 'a m_space) (d : 'a -> 'a -> real)
      (s : 'a set) (t : 'i set) (C : real)
      (r : 'i -> real) (c : 'i -> 'a) (B : 'i -> 'a set).
      measure_space m /\
      m_space m = UNIV /\
      q3229352_pseudo_metric d /\
      q3229352_second_countable d /\
      q3229352_opens_measurable m d /\
      q3229352_locally_finite m d /\
      0 <= C /\
      (!a.
        a IN t ==>
        B a SUBSET q3229352_closed_ball d (c a) (r a)) /\
      (!a.
        a IN t ==>
        q3229352_outer_measure m
          (q3229352_closed_ball d (c a) (3 * r a)) <=
        Normal C * q3229352_outer_measure m (B a)) /\
      (!a.
        a IN t ==>
        q3229352_nonempty_interior d (B a)) /\
      (!a.
        a IN t ==>
        q3229352_closed d (B a)) /\
      (!x epsilon.
        x IN s /\ 0 < epsilon ==>
        ?a.
          a IN t /\
          r a <= epsilon /\
          c a = x)
      ==>
      ?u : 'i set.
        u SUBSET t /\
        COUNTABLE u /\
        q3229352_pairwise_disjoint u B /\
        q3229352_outer_measure m
          (s DIFF BIGUNION (IMAGE B u)) = Normal 0``;
