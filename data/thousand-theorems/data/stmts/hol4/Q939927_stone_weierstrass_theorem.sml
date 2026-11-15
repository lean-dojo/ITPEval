(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q939927, "Stone–Weierstrass theorem": a real subalgebra of continuous
  functions on a compact topological space is uniformly dense when it
  separates points. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory topologyTheory real_topologyTheory;

val q939927_real_subalgebra_def = new_definition (
  "q939927_real_subalgebra_def",
  ``q939927_real_subalgebra
      (top : 'a topology) (A : ('a -> real) set) <=>
      (!f.
        f IN A
        ==>
        continuous_map (top,euclidean) f) /\
      (!c : real. (\x. c) IN A) /\
      (!f g.
        f IN A /\ g IN A
        ==>
        (\x. f x + g x) IN A) /\
      (!f g.
        f IN A /\ g IN A
        ==>
        (\x. f x * g x) IN A)``);

val q939927_separates_points_def = new_definition (
  "q939927_separates_points_def",
  ``q939927_separates_points (A : ('a -> real) set) <=>
      !x y.
        x <> y
        ==>
        ?f. f IN A /\ f x <> f y``);

val q939927_uniformly_dense_def = new_definition (
  "q939927_uniformly_dense_def",
  ``q939927_uniformly_dense
      (top : 'a topology) (A : ('a -> real) set) <=>
      !f.
        continuous_map (top,euclidean) f
        ==>
        !epsilon : real.
          0 < epsilon
          ==>
          ?g.
            g IN A /\
            !x. abs (g x - f x) < epsilon``);

val ContinuousMap_subalgebra_topologicalClosure_eq_top_of_separatesPoints =
  ``!(top : 'a topology) (A : ('a -> real) set).
      topspace top = UNIV /\
      compact_in top UNIV /\
      q939927_real_subalgebra top A /\
      q939927_separates_points A
      ==>
      q939927_uniformly_dense top A``;
