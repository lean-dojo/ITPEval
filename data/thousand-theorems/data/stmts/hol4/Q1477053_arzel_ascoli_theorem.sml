(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1477053 (thousand-theorems__hol4__Q1477053), "Arzelà–Ascoli theorem":
  a pointwise equicontinuous family of bounded continuous functions from a
  compact space, with values in a common compact metric subset, has compact
  uniform closure. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory realTheory;

val q1477053_metric_def = new_definition (
  "q1477053_metric_def",
  ``q1477053_metric (dist : 'b -> 'b -> real) <=>
      (!x. dist x x = 0) /\
      (!x y. 0 <= dist x y) /\
      (!x y. dist x y = dist y x) /\
      (!x y. (dist x y = 0) <=> (x = y)) /\
      (!x y z. dist x z <= dist x y + dist y z)``);

val q1477053_continuous_def = new_definition (
  "q1477053_continuous_def",
  ``q1477053_continuous
      (top : 'a topology) (dist : 'b -> 'b -> real)
      (f : 'a -> 'b) <=>
      !x epsilon.
        0 < epsilon ==>
        ?u.
          open_in top u /\
          x IN u /\
          !y. y IN u ==> dist (f y) (f x) < epsilon``);

val q1477053_bounded_def = new_definition (
  "q1477053_bounded_def",
  ``q1477053_bounded
      (dist : 'b -> 'b -> real) (f : 'a -> 'b) <=>
      ?C : real.
        0 <= C /\
        !x y. dist (f x) (f y) <= C``);

val q1477053_bounded_continuous_def = new_definition (
  "q1477053_bounded_continuous_def",
  ``q1477053_bounded_continuous
      (top : 'a topology) (dist : 'b -> 'b -> real)
      (f : 'a -> 'b) <=>
      q1477053_continuous top dist f /\
      q1477053_bounded dist f``);

val q1477053_metric_open_in_def = new_definition (
  "q1477053_metric_open_in_def",
  ``q1477053_metric_open_in
      (dist : 'b -> 'b -> real) (s : 'b set) (u : 'b set) <=>
      u SUBSET s /\
      !x.
        x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            y IN s /\ dist y x < epsilon
            ==>
            y IN u``);

val q1477053_metric_compact_def = new_definition (
  "q1477053_metric_compact_def",
  ``q1477053_metric_compact
      (dist : 'b -> 'b -> real) (s : 'b set) <=>
      !cover : ('b set) set.
        (!u. u IN cover ==> q1477053_metric_open_in dist s u) /\
        s SUBSET BIGUNION cover
        ==>
        ?subcover : ('b set) set.
          subcover SUBSET cover /\
          FINITE subcover /\
          s SUBSET BIGUNION subcover``);

val q1477053_equicontinuous_def = new_definition (
  "q1477053_equicontinuous_def",
  ``q1477053_equicontinuous
      (top : 'a topology) (dist : 'b -> 'b -> real)
      (A : ('a -> 'b) set) <=>
      !x epsilon.
        0 < epsilon ==>
        ?u.
          open_in top u /\
          x IN u /\
          !f y.
            f IN A /\ y IN u
            ==>
            dist (f y) (f x) < epsilon``);

val q1477053_uniform_open_def = new_definition (
  "q1477053_uniform_open_def",
  ``q1477053_uniform_open
      (top : 'a topology) (dist : 'b -> 'b -> real)
      (u : ('a -> 'b) set) <=>
      u SUBSET
        {f | q1477053_bounded_continuous top dist f} /\
      !f.
        f IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !g.
            q1477053_bounded_continuous top dist g /\
            (!x. dist (g x) (f x) < epsilon)
            ==>
            g IN u``);

val q1477053_uniform_closure_def = new_definition (
  "q1477053_uniform_closure_def",
  ``q1477053_uniform_closure
      (top : 'a topology) (dist : 'b -> 'b -> real)
      (A : ('a -> 'b) set) =
      {f |
        q1477053_bounded_continuous top dist f /\
        !epsilon : real.
          0 < epsilon ==>
          ?g.
            g IN A /\
            !x. dist (f x) (g x) < epsilon}``);

val q1477053_uniformly_compact_def = new_definition (
  "q1477053_uniformly_compact_def",
  ``q1477053_uniformly_compact
      (top : 'a topology) (dist : 'b -> 'b -> real)
      (function_set : ('a -> 'b) set) <=>
      !cover : (('a -> 'b) set) set.
        (!u. u IN cover ==> q1477053_uniform_open top dist u) /\
        function_set SUBSET BIGUNION cover
        ==>
        ?subcover : (('a -> 'b) set) set.
          subcover SUBSET cover /\
          FINITE subcover /\
          function_set SUBSET BIGUNION subcover``);

val BoundedContinuousFunction_arzela_ascoli =
  ``!(top : 'a topology) (dist : 'b -> 'b -> real)
      (s : 'b set) (A : ('a -> 'b) set).
      topspace top = UNIV /\
      compact_in top UNIV /\
      q1477053_metric dist /\
      q1477053_metric_compact dist s /\
      (!f.
        f IN A
        ==>
        q1477053_bounded_continuous top dist f) /\
      (!f x. f IN A ==> f x IN s) /\
      q1477053_equicontinuous top dist A
      ==>
      q1477053_uniformly_compact top dist
        (q1477053_uniform_closure top dist A)``;
