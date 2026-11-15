(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q137164, "Besicovitch covering theorem": admissible closed balls with
  arbitrarily small radii admit a countable pairwise-disjoint subfamily
  covering the given set up to a null remainder. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open measureTheory;

val q137164_metric_space_def = new_definition (
  "q137164_metric_space_def",
  ``q137164_metric_space (d : 'a -> 'a -> real) <=>
      (!x. d x x = 0) /\
      (!x y. 0 <= d x y) /\
      (!x y. d x y = d y x) /\
      (!x y. d x y = 0 <=> x = y) /\
      (!x y z. d x z <= d x y + d y z)``);

val q137164_open_def = new_definition (
  "q137164_open_def",
  ``q137164_open (d : 'a -> 'a -> real) (u : 'a set) <=>
      !x.
        x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. d y x < epsilon ==> y IN u``);

val q137164_second_countable_def = new_definition (
  "q137164_second_countable_def",
  ``q137164_second_countable (d : 'a -> 'a -> real) <=>
      ?basis : ('a set) set.
        COUNTABLE basis /\
        (!v. v IN basis ==> q137164_open d v) /\
        !u x.
          q137164_open d u /\ x IN u
          ==>
          ?v. v IN basis /\ x IN v /\ v SUBSET u``);

val q137164_opens_measurable_def = new_definition (
  "q137164_opens_measurable_def",
  ``q137164_opens_measurable
      (d : 'a -> 'a -> real) (m : 'a m_space) <=>
      !u. q137164_open d u ==> u IN measurable_sets m``);

val q137164_closed_ball_def = new_definition (
  "q137164_closed_ball_def",
  ``q137164_closed_ball
      (d : 'a -> 'a -> real) (x : 'a) (radius : real) =
      {y | d y x <= radius}``);

val q137164_satellite_config_def = new_definition (
  "q137164_satellite_config_def",
  ``q137164_satellite_config
      (d : 'a -> 'a -> real) (N : num) (tau : real)
      (c : num -> 'a) (r : num -> real) <=>
      (!i. i <= N ==> 0 < r i) /\
      (!i j.
        i <= N /\ j <= N /\ i <> j
        ==>
        ((r i <= d (c i) (c j) /\ r j <= tau * r i) \/
         (r j <= d (c j) (c i) /\ r i <= tau * r j))) /\
      (!i.
        i < N ==>
        r i <= d (c i) (c N) /\ r N <= tau * r i) /\
      (!i.
        i < N ==>
        d (c i) (c N) <= r i + r N)``);

val q137164_has_besicovitch_covering_def = new_definition (
  "q137164_has_besicovitch_covering_def",
  ``q137164_has_besicovitch_covering
      (d : 'a -> 'a -> real) <=>
      ?N : num. ?tau : real.
        1 < tau /\
        ~(?c : num -> 'a. ?r : num -> real.
            q137164_satellite_config d N tau c r)``);

val q137164_sfinite_def = new_definition (
  "q137164_sfinite_def",
  ``q137164_sfinite (m : 'a m_space) <=>
      ?parts : num -> 'a set -> extreal.
        (!n.
          measure_space (m_space m,measurable_sets m,parts n) /\
          parts n (m_space m) <> PosInf) /\
        !u.
          u IN measurable_sets m ==>
          measure m u = suminf (\n. parts n u)``);

val q137164_outer_measure_def = new_definition (
  "q137164_outer_measure_def",
  ``q137164_outer_measure (m : 'a m_space) (u : 'a set) =
      inf
        {z : extreal |
          ?v : 'a set.
            u SUBSET v /\
            v IN measurable_sets m /\
            measure m v = z}``);

val q137164_pairwise_disjoint_def = new_definition (
  "q137164_pairwise_disjoint_def",
  ``q137164_pairwise_disjoint
      (d : 'a -> 'a -> real) (t : 'a set) (r : 'a -> real) <=>
      !x y.
        x IN t /\ y IN t /\ x <> y
        ==>
        DISJOINT
          (q137164_closed_ball d x (r x))
          (q137164_closed_ball d y (r y))``);

val exists_disjoint_closedBall_covering_ae =
  ``!(m : 'a m_space) (d : 'a -> 'a -> real)
      (f : 'a -> real set) (s : 'a set) (R : 'a -> real).
      measure_space m /\
      m_space m = UNIV /\
      q137164_metric_space d /\
      q137164_second_countable d /\
      q137164_opens_measurable d m /\
      q137164_sfinite m /\
      q137164_has_besicovitch_covering d /\
      (!x.
        x IN s ==>
        !delta : real.
          0 < delta ==>
          ?radius : real.
            radius IN f x /\
            0 < radius /\
            radius < delta) /\
      (!x. x IN s ==> 0 < R x)
      ==>
      ?t : 'a set. ?r : 'a -> real.
        COUNTABLE t /\
        t SUBSET s /\
        (!x.
          x IN t ==>
          r x IN f x /\
          0 < r x /\
          r x < R x) /\
        q137164_outer_measure m
          (s DIFF
            BIGUNION
              (IMAGE
                (\x. q137164_closed_ball d x (r x))
                t)) = 0 /\
        q137164_pairwise_disjoint d t r``;
