(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q7249519 (thousand-theorems__hol4__Q7249519), "Prokhorov's theorem":
  on a possibly empty Hausdorff Borel space, finite measures with uniformly
  bounded mass and vanishing compact-tail bounds form a compact set in the
  weak topology when the space is normal or the compact sets are nested.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory sigma_algebraTheory measureTheory;
open borelTheory lebesgueTheory;

val q7249519_t2_space_def = new_definition (
  "q7249519_t2_space_def",
  ``q7249519_t2_space (top : 'a topology) <=>
      !x y.
        x IN topspace top /\
        y IN topspace top /\
        x <> y
        ==>
        ?u v.
          open_in top u /\
          open_in top v /\
          x IN u /\
          y IN v /\
          DISJOINT u v``);

val q7249519_normal_space_def = new_definition (
  "q7249519_normal_space_def",
  ``q7249519_normal_space (top : 'a topology) <=>
      !s t.
        closed_in top s /\
        closed_in top t /\
        DISJOINT s t
        ==>
        ?u v.
          open_in top u /\
          open_in top v /\
          s SUBSET u /\
          t SUBSET v /\
          DISJOINT u v``);

val q7249519_borel_space_def = new_definition (
  "q7249519_borel_space_def",
  ``q7249519_borel_space
      (top : 'a topology) (meas : 'a algebra) <=>
      meas = general_borel top``);

val q7249519_finite_borel_measure_def = new_definition (
  "q7249519_finite_borel_measure_def",
  ``q7249519_finite_borel_measure
      (top : 'a topology) (meas : 'a algebra) (mu : 'a m_space) <=>
      finite_measure_space mu /\
      m_space mu = topspace top /\
      measurable_sets mu = subsets meas``);

val q7249519_real_integral_def = new_definition (
  "q7249519_real_integral_def",
  ``q7249519_real_integral
      (mu : 'a m_space) (f : 'a -> real) =
      real (integral mu (Normal o f))``);

val q7249519_bounded_continuous_def = new_definition (
  "q7249519_bounded_continuous_def",
  ``q7249519_bounded_continuous
      (top : 'a topology) (f : 'a -> real) <=>
      continuous_map (top,euclidean) f /\
      bounded (IMAGE f (topspace top))``);

val q7249519_weak_subbasic_def = new_definition (
  "q7249519_weak_subbasic_def",
  ``q7249519_weak_subbasic
      (top : 'a topology) (meas : 'a algebra)
      (s : ('a m_space) set) <=>
      ?f v.
        q7249519_bounded_continuous top f /\
        open_in euclidean v /\
        s =
          {mu |
            q7249519_finite_borel_measure top meas mu /\
            q7249519_real_integral mu f IN v}``);

val q7249519_weak_basic_def = new_definition (
  "q7249519_weak_basic_def",
  ``q7249519_weak_basic
      (top : 'a topology) (meas : 'a algebra)
      (b : ('a m_space) set) <=>
      ?F : (('a m_space) set) set.
        FINITE F /\
        (!s. s IN F ==> q7249519_weak_subbasic top meas s) /\
        b =
          {mu | q7249519_finite_borel_measure top meas mu} INTER
          BIGINTER F``);

val q7249519_weak_open_def = new_definition (
  "q7249519_weak_open_def",
  ``q7249519_weak_open
      (top : 'a topology) (meas : 'a algebra)
      (s : ('a m_space) set) <=>
      ?B : (('a m_space) set) set.
        (!b. b IN B ==> q7249519_weak_basic top meas b) /\
        s = BIGUNION B``);

val q7249519_weak_topology_def = new_definition (
  "q7249519_weak_topology_def",
  ``q7249519_weak_topology
      (top : 'a topology) (meas : 'a algebra) =
      topology {s | q7249519_weak_open top meas s}``);

val prokhorov_s_theorem =
  ``!(top : 'a topology) (meas : 'a algebra)
      (u : num -> real) (K : num -> 'a set) (C : real).
      q7249519_t2_space top /\
      q7249519_borel_space top meas /\
      0 <= C /\
      (!n. 0 <= u n) /\
      ((u --> 0) sequentially) /\
      (!n. compact_in top (K n)) /\
      (q7249519_normal_space top \/
       !m n. m <= n ==> K m SUBSET K n)
      ==>
      compact_in
        (q7249519_weak_topology top meas)
        {mu |
          q7249519_finite_borel_measure top meas mu /\
          measure mu (m_space mu) <= Normal C /\
          !n.
            measure mu (m_space mu DIFF K n) <= Normal (u n)}``;
