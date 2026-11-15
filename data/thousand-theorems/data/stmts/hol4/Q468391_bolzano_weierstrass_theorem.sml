(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q468391, "Bolzano–Weierstrass theorem": in a proper pseudo-metric space,
  a sequence frequently contained in a bounded set, and hence a sequence
  contained in that set, has a convergent subsequence whose limit lies in
  the set's closure. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val q468391_pseudo_metric_def = new_definition (
  "q468391_pseudo_metric_def",
  ``q468391_pseudo_metric (dist : 'a -> 'a -> real) <=>
      (!x. dist x x = 0) /\
      (!x y. 0 <= dist x y) /\
      (!x y. dist x y = dist y x) /\
      (!x y z. dist x z <= dist x y + dist y z)``);

val q468391_open_def = new_definition (
  "q468391_open_def",
  ``q468391_open (dist : 'a -> 'a -> real) (u : 'a set) <=>
      !x.
        x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. dist y x < epsilon ==> y IN u``);

val q468391_compact_def = new_definition (
  "q468391_compact_def",
  ``q468391_compact (dist : 'a -> 'a -> real) (k : 'a set) <=>
      !cover : ('a set) set.
        (!u. u IN cover ==> q468391_open dist u) /\
        k SUBSET BIGUNION cover
        ==>
        ?subcover : ('a set) set.
          subcover SUBSET cover /\
          FINITE subcover /\
          k SUBSET BIGUNION subcover``);

val q468391_closed_ball_def = new_definition (
  "q468391_closed_ball_def",
  ``q468391_closed_ball
      (dist : 'a -> 'a -> real) (x : 'a) (radius : real) =
      {y | dist y x <= radius}``);

val q468391_proper_space_def = new_definition (
  "q468391_proper_space_def",
  ``q468391_proper_space (dist : 'a -> 'a -> real) <=>
      !x radius.
        q468391_compact dist (q468391_closed_ball dist x radius)``);

val q468391_bounded_def = new_definition (
  "q468391_bounded_def",
  ``q468391_bounded (dist : 'a -> 'a -> real) (s : 'a set) <=>
      ?bound : real.
        !x y.
          x IN s /\ y IN s
          ==>
          dist x y <= bound``);

val q468391_in_closure_def = new_definition (
  "q468391_in_closure_def",
  ``q468391_in_closure
      (dist : 'a -> 'a -> real) (s : 'a set) (a : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?y. y IN s /\ dist y a < epsilon``);

val q468391_frequently_in_def = new_definition (
  "q468391_frequently_in_def",
  ``q468391_frequently_in (x : num -> 'a) (s : 'a set) <=>
      !N : num.
        ?n : num. N <= n /\ x n IN s``);

val q468391_strict_mono_def = new_definition (
  "q468391_strict_mono_def",
  ``q468391_strict_mono (phi : num -> num) <=>
      !m n : num. m < n ==> phi m < phi n``);

val q468391_tendsto_def = new_definition (
  "q468391_tendsto_def",
  ``q468391_tendsto
      (dist : 'a -> 'a -> real) (u : num -> 'a) (a : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num. N <= n ==> dist (u n) a < epsilon``);

val tendsto_subseq_of_frequently_bounded =
  ``!(dist : 'a -> 'a -> real) (s : 'a set) (x : num -> 'a).
      q468391_pseudo_metric dist /\
      q468391_proper_space dist /\
      q468391_bounded dist s /\
      q468391_frequently_in x s
      ==>
      ?a : 'a.
        q468391_in_closure dist s a /\
        ?phi : num -> num.
          q468391_strict_mono phi /\
          q468391_tendsto dist (\n. x (phi n)) a``;

val tendsto_subseq_of_bounded =
  ``!(dist : 'a -> 'a -> real) (s : 'a set) (x : num -> 'a).
      q468391_pseudo_metric dist /\
      q468391_proper_space dist /\
      q468391_bounded dist s /\
      (!n : num. x n IN s)
      ==>
      ?a : 'a.
        q468391_in_closure dist s a /\
        ?phi : num -> num.
          q468391_strict_mono phi /\
          q468391_tendsto dist (\n. x (phi n)) a``;
