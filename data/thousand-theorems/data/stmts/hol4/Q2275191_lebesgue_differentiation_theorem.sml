(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2275191, "Lebesgue differentiation theorem": for a nonnegative
  almost-everywhere measurable function with finite lower integral, its
  restricted lower-integral averages along any Vitali family converge almost
  everywhere to the function. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory lebesgueTheory;

val q2275191_pseudo_metric_def = new_definition (
  "q2275191_pseudo_metric_def",
  ``q2275191_pseudo_metric
      (space : 'a set) (dist : 'a -> 'a -> real) <=>
      (!x. x IN space ==> dist x x = 0) /\
      (!x y. x IN space /\ y IN space ==> 0 <= dist x y) /\
      (!x y. x IN space /\ y IN space ==> dist x y = dist y x) /\
      (!x y z.
        x IN space /\ y IN space /\ z IN space ==>
        dist x z <= dist x y + dist y z)``);

val q2275191_closed_ball_def = new_definition (
  "q2275191_closed_ball_def",
  ``q2275191_closed_ball
      (space : 'a set) (dist : 'a -> 'a -> real)
      (x : 'a) (radius : real) =
      {y | y IN space /\ dist y x <= radius}``);

val q2275191_open_def = new_definition (
  "q2275191_open_def",
  ``q2275191_open
      (space : 'a set) (dist : 'a -> 'a -> real) (u : 'a set) <=>
      u SUBSET space /\
      !x.
        x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            y IN space /\ dist y x < epsilon ==>
            y IN u``);

val q2275191_second_countable_def = new_definition (
  "q2275191_second_countable_def",
  ``q2275191_second_countable
      (space : 'a set) (dist : 'a -> 'a -> real) <=>
      ?basis : ('a set) set.
        COUNTABLE basis /\
        (!v. v IN basis ==> q2275191_open space dist v) /\
        !u x.
          q2275191_open space dist u /\ x IN u ==>
          ?v.
            v IN basis /\
            x IN v /\
            v SUBSET u``);

val q2275191_borel_space_def = new_definition (
  "q2275191_borel_space_def",
  ``q2275191_borel_space
      (m : 'a m_space) (dist : 'a -> 'a -> real) <=>
      measurable_sets m =
        subsets
          (sigma (m_space m)
            {u : 'a set |
              q2275191_open (m_space m) dist u})``);

val q2275191_locally_finite_def = new_definition (
  "q2275191_locally_finite_def",
  ``q2275191_locally_finite
      (m : 'a m_space) (dist : 'a -> 'a -> real) <=>
      !x.
        x IN m_space m ==>
        ?u : 'a set.
          q2275191_open (m_space m) dist u /\
          x IN u /\
          measure m u <> PosInf``);

val q2275191_outer_measure_def = new_definition (
  "q2275191_outer_measure_def",
  ``q2275191_outer_measure (m : 'a m_space) (s : 'a set) =
      inf
        {r : extreal |
          ?t : 'a set.
            s SUBSET t /\
            t IN measurable_sets m /\
            measure m t = r}``);

val q2275191_nonempty_interior_def = new_definition (
  "q2275191_nonempty_interior_def",
  ``q2275191_nonempty_interior
      (space : 'a set) (dist : 'a -> 'a -> real) (s : 'a set) <=>
      ?u y.
        q2275191_open space dist u /\
        y IN u /\
        u SUBSET s``);

val q2275191_pairwise_disjoint_snd_def = new_definition (
  "q2275191_pairwise_disjoint_snd_def",
  ``q2275191_pairwise_disjoint_snd
      (t : ('a # ('a set)) set) <=>
      !p q.
        p IN t /\ q IN t /\ p <> q ==>
        DISJOINT (SND p) (SND q)``);

val q2275191_vitali_family_def = new_definition (
  "q2275191_vitali_family_def",
  ``q2275191_vitali_family
      (m : 'a m_space) (dist : 'a -> 'a -> real)
      (setsAt : 'a -> ('a set) set) <=>
      (!x s.
        x IN m_space m /\ s IN setsAt x ==>
        s IN measurable_sets m) /\
      (!x s.
        x IN m_space m /\ s IN setsAt x ==>
        q2275191_nonempty_interior (m_space m) dist s) /\
      (!x epsilon.
        x IN m_space m /\ 0 < epsilon ==>
        ?s.
          s IN setsAt x /\
          s SUBSET
            q2275191_closed_ball (m_space m) dist x epsilon) /\
      (!s subfamily.
        s SUBSET m_space m /\
        (!x.
          x IN s ==>
          subfamily x SUBSET setsAt x) /\
        (!x epsilon.
          x IN s /\ 0 < epsilon ==>
          ?t.
            t IN subfamily x /\
            t SUBSET
              q2275191_closed_ball
                (m_space m) dist x epsilon)
        ==>
        ?t : ('a # ('a set)) set.
          (!p. p IN t ==> FST p IN s) /\
          q2275191_pairwise_disjoint_snd t /\
          (!p. p IN t ==> SND p IN subfamily (FST p)) /\
          q2275191_outer_measure m
            (s DIFF BIGUNION (IMAGE SND t)) = Normal 0)``);

val q2275191_ae_measurable_def = new_definition (
  "q2275191_ae_measurable_def",
  ``q2275191_ae_measurable
      (m : 'a m_space) (f : 'a -> extreal) <=>
      ?g : 'a -> extreal.
        (!x. x IN m_space m ==> 0 <= g x) /\
        g IN measurable (m_space m,measurable_sets m) Borel /\
        (AE x::m. f x = g x)``);

val q2275191_ennreal_div_def = new_definition (
  "q2275191_ennreal_div_def",
  ``q2275191_ennreal_div (x : extreal) (y : extreal) =
      if y = PosInf then Normal 0
      else if y = Normal 0 then
        if x = Normal 0 then Normal 0 else PosInf
      else x / y``);

val q2275191_lintegral_on_def = new_definition (
  "q2275191_lintegral_on_def",
  ``q2275191_lintegral_on
      (m : 'a m_space) (f : 'a -> extreal) (s : 'a set) =
      pos_fn_integral m
        (\x. f x * indicator_fn s x)``);

val q2275191_tendsto_filterAt_def = new_definition (
  "q2275191_tendsto_filterAt_def",
  ``q2275191_tendsto_filterAt
      (space : 'a set) (dist : 'a -> 'a -> real)
      (setsAt : 'a -> ('a set) set) (x : 'a)
      (u : ('a set) -> extreal) (ell : extreal) <=>
      (ell = PosInf /\
       !bound : real.
         ?delta : real.
           0 < delta /\
           !a.
             a IN setsAt x /\
             a SUBSET q2275191_closed_ball space dist x delta
             ==>
             Normal bound < u a) \/
      (?limit : real.
        ell = Normal limit /\
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !a.
              a IN setsAt x /\
              a SUBSET q2275191_closed_ball space dist x delta
              ==>
              Normal (limit - epsilon) < u a /\
              u a < Normal (limit + epsilon))``);

val ae_tendsto_lintegral_div =
  ``!(m : 'a m_space) (dist : 'a -> 'a -> real)
      (setsAt : 'a -> ('a set) set) (f : 'a -> extreal).
      measure_space m /\
      m_space m = UNIV /\
      q2275191_pseudo_metric (m_space m) dist /\
      q2275191_second_countable (m_space m) dist /\
      q2275191_borel_space m dist /\
      q2275191_locally_finite m dist /\
      q2275191_vitali_family m dist setsAt /\
      (!x. x IN m_space m ==> 0 <= f x) /\
      q2275191_ae_measurable m f /\
      pos_fn_integral m f <> PosInf
      ==>
      (AE x::m.
        q2275191_tendsto_filterAt
          (m_space m) dist setsAt x
          (\a.
            q2275191_ennreal_div
              (q2275191_lintegral_on m f a)
              (measure m a))
          (f x))``;
