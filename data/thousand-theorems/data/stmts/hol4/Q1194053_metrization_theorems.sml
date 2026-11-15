(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1194053 (thousand-theorems__hol4__Q1194053), "Metrization theorems":
  every T3 topological space with a second-countable topology admits a
  compatible metric. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory realTheory;

val q1194053_t0_space_def = new_definition (
  "q1194053_t0_space_def",
  ``q1194053_t0_space (top : 'a topology) <=>
      !(x : 'a) (y : 'a).
        x IN topspace top /\ y IN topspace top /\ ~(x = y)
        ==>
        ?(u : 'a set).
          open_in top u /\
          ((x IN u /\ ~(y IN u)) \/ (y IN u /\ ~(x IN u)))``);

val q1194053_regular_space_def = new_definition (
  "q1194053_regular_space_def",
  ``q1194053_regular_space (top : 'a topology) <=>
      !(s : 'a set) (a : 'a).
        closed_in top s /\ a IN topspace top /\ ~(a IN s)
        ==>
        ?(u : 'a set) (v : 'a set).
          open_in top u /\
          open_in top v /\
          s SUBSET u /\
          a IN v /\
          DISJOINT u v``);

val q1194053_t3_space_def = new_definition (
  "q1194053_t3_space_def",
  ``q1194053_t3_space (top : 'a topology) <=>
      q1194053_t0_space top /\ q1194053_regular_space top``);

val q1194053_second_countable_def = new_definition (
  "q1194053_second_countable_def",
  ``q1194053_second_countable (top : 'a topology) <=>
      ?(basis : ('a set) set).
        COUNTABLE basis /\
        (!(v : 'a set). v IN basis ==> open_in top v) /\
        !(u : 'a set) (x : 'a).
          open_in top u /\ x IN u
          ==>
          ?(v : 'a set). v IN basis /\ x IN v /\ v SUBSET u``);

val q1194053_metrizable_space_def = new_definition (
  "q1194053_metrizable_space_def",
  ``q1194053_metrizable_space (top : 'a topology) <=>
      ?(d : 'a -> 'a -> real).
        (!(x : 'a) (y : 'a).
          x IN topspace top /\ y IN topspace top
          ==>
          0 <= d x y /\
          (d x y = 0 <=> x = y) /\
          d x y = d y x) /\
        (!(x : 'a) (y : 'a) (z : 'a).
          x IN topspace top /\
          y IN topspace top /\
          z IN topspace top
          ==>
          d x z <= d x y + d y z) /\
        !(u : 'a set).
          open_in top u <=>
          u SUBSET topspace top /\
          !(x : 'a).
            x IN u
            ==>
            ?(r : real).
              0 < r /\
              !(y : 'a).
                y IN topspace top /\ d x y < r
                ==>
                y IN u``);

val TopologicalSpace_metrizableSpace_of_t3_secondCountable =
  ``!(top : 'a topology).
      q1194053_t3_space top /\
      q1194053_second_countable top
      ==>
      q1194053_metrizable_space top``;
