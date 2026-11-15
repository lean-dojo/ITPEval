(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q842953, "Lebesgue's density theorem": in a second-countable metric space
  with the Besicovitch covering property, almost every point of an arbitrary
  set is a density point for every locally finite Borel measure. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory;

val q842953_metric_space_def = new_definition (
  "q842953_metric_space_def",
  ``q842953_metric_space (d : 'a -> 'a -> real) <=>
      (!x. d x x = 0) /\
      (!x y. 0 <= d x y) /\
      (!x y. d x y = d y x) /\
      (!x y. d x y = 0 <=> x = y) /\
      (!x y z. d x z <= d x y + d y z)``);

val q842953_open_def = new_definition (
  "q842953_open_def",
  ``q842953_open (d : 'a -> 'a -> real) (u : 'a set) <=>
      !x.
        x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. d y x < epsilon ==> y IN u``);

val q842953_second_countable_def = new_definition (
  "q842953_second_countable_def",
  ``q842953_second_countable (d : 'a -> 'a -> real) <=>
      ?basis : ('a set) set.
        COUNTABLE basis /\
        (!v. v IN basis ==> q842953_open d v) /\
        !u x.
          q842953_open d u /\ x IN u ==>
          ?v.
            v IN basis /\
            x IN v /\
            v SUBSET u``);

val q842953_borel_space_def = new_definition (
  "q842953_borel_space_def",
  ``q842953_borel_space
      (m : 'a m_space) (d : 'a -> 'a -> real) <=>
      measurable_sets m =
        subsets
          (sigma (m_space m)
            {u : 'a set | q842953_open d u})``);

val q842953_outer_measure_def = new_definition (
  "q842953_outer_measure_def",
  ``q842953_outer_measure (m : 'a m_space) (s : 'a set) =
      inf
        {value : extreal |
          ?measurable_superset : 'a set.
            s SUBSET measurable_superset /\
            measurable_superset IN measurable_sets m /\
            measure m measurable_superset = value}``);

val q842953_locally_finite_def = new_definition (
  "q842953_locally_finite_def",
  ``q842953_locally_finite
      (m : 'a m_space) (d : 'a -> 'a -> real) <=>
      !x.
        ?u : 'a set.
          q842953_open d u /\
          x IN u /\
          measure m u <> PosInf``);

val q842953_closed_ball_def = new_definition (
  "q842953_closed_ball_def",
  ``q842953_closed_ball
      (d : 'a -> 'a -> real) (x : 'a) (radius : real) =
      {y | d y x <= radius}``);

val q842953_satellite_config_def = new_definition (
  "q842953_satellite_config_def",
  ``q842953_satellite_config
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

val q842953_has_besicovitch_covering_def = new_definition (
  "q842953_has_besicovitch_covering_def",
  ``q842953_has_besicovitch_covering
      (d : 'a -> 'a -> real) <=>
      ?N : num. ?tau : real.
        1 < tau /\
        ~(?c : num -> 'a. ?r : num -> real.
            q842953_satellite_config d N tau c r)``);

val q842953_ennreal_div_def = new_definition (
  "q842953_ennreal_div_def",
  ``q842953_ennreal_div (x : extreal) (y : extreal) =
      if y = PosInf then Normal 0
      else if y = Normal 0 then
        if x = Normal 0 then Normal 0 else PosInf
      else x / y``);

val q842953_tendsto_zero_right_one_def = new_definition (
  "q842953_tendsto_zero_right_one_def",
  ``q842953_tendsto_zero_right_one (f : real -> extreal) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !radius : real.
            0 < radius /\ radius < delta ==>
            Normal (1 - epsilon) < f radius /\
            f radius < Normal (1 + epsilon)``);

val q842953_restrict_def = new_definition (
  "q842953_restrict_def",
  ``q842953_restrict (m : 'a m_space) (s : 'a set) =
      (m_space m, measurable_sets m,
       \t. q842953_outer_measure m (t INTER s))``);

val lebesgue_density_theorem =
  ``!(m : 'a m_space) (d : 'a -> 'a -> real) (s : 'a set).
      measure_space m /\
      m_space m = UNIV /\
      q842953_metric_space d /\
      q842953_second_countable d /\
      q842953_borel_space m d /\
      q842953_locally_finite m d /\
      q842953_has_besicovitch_covering d
      ==>
      (AE x::(q842953_restrict m s).
          q842953_tendsto_zero_right_one
            (\radius.
              q842953_ennreal_div
                (q842953_outer_measure m
                  (s INTER q842953_closed_ball d x radius))
                (q842953_outer_measure m
                  (q842953_closed_ball d x radius))))``;
