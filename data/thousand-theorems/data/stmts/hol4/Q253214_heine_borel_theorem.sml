(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q253214 (thousand-theorems__hol4__Q253214), "Heine–Borel theorem": in a
  proper metric space, a set is compact if and only if it is closed and
  bounded. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory metricTheory realTheory;

val q253214_is_bounded_def = new_definition (
  "q253214_is_bounded_def",
  ``q253214_is_bounded (m : 'a metric) (s : 'a set) <=>
      ?c.
        !x y.
          x IN s /\ y IN s
          ==>
          dist m (x,y) <= c``);

val q253214_proper_space_def = new_definition (
  "q253214_proper_space_def",
  ``q253214_proper_space (m : 'a metric) <=>
      !x r.
        compact_in (mtopology m) (mcball m (x,r))``);

val Metric_isCompact_iff_isClosed_bounded =
  ``!(m : 'a metric) (s : 'a set).
      q253214_proper_space m
      ==>
      (compact_in (mtopology m) s <=>
       closed_in (mtopology m) s /\
       q253214_is_bounded m s)``;
