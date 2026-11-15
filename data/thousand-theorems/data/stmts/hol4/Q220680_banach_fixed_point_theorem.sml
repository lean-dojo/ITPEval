(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q220680, "Banach fixed-point theorem": a contraction on a complete extended
  metric space has a fixed point approached by its iterates with the standard
  geometric error bound. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory extrealTheory;

val q220680_emetric_space_def = new_definition (
  "q220680_emetric_space_def",
  ``q220680_emetric_space (edist : 'a -> 'a -> extreal) <=>
      (!x y : 'a. 0 <= edist x y) /\
      (!x y : 'a. (edist x y = 0) <=> (x = y)) /\
      (!x y : 'a. edist x y = edist y x) /\
      (!x y z : 'a. edist x z <= edist x y + edist y z)``);

val q220680_tendsto_def = new_definition (
  "q220680_tendsto_def",
  ``q220680_tendsto
      (edist : 'a -> 'a -> extreal) (u : num -> 'a) (y : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> edist (u n) y < Normal epsilon``);

val q220680_cauchy_def = new_definition (
  "q220680_cauchy_def",
  ``q220680_cauchy
      (edist : 'a -> 'a -> extreal) (u : num -> 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          edist (u m) (u n) < Normal epsilon``);

val q220680_complete_emetric_space_def = new_definition (
  "q220680_complete_emetric_space_def",
  ``q220680_complete_emetric_space
      (edist : 'a -> 'a -> extreal) <=>
      !u : num -> 'a.
        q220680_cauchy edist u ==>
        ?y : 'a. q220680_tendsto edist u y``);

val q220680_contracting_with_def = new_definition (
  "q220680_contracting_with_def",
  ``q220680_contracting_with
      (k : real) (edist : 'a -> 'a -> extreal) (f : 'a -> 'a) <=>
      0 <= k /\
      k < 1 /\
      !x y : 'a.
        edist (f x) (f y) <= Normal k * edist x y``);

val ContractingWith_exists_fixedPoint =
  ``!(edist : 'a -> 'a -> extreal)
      (f : 'a -> 'a) (k : real) (x : 'a).
      q220680_emetric_space edist /\
      q220680_complete_emetric_space edist /\
      q220680_contracting_with k edist f /\
      edist x (f x) <> PosInf
      ==>
      ?y : 'a.
        f y = y /\
        q220680_tendsto edist (\n. FUNPOW f n x) y /\
        !n : num.
          edist (FUNPOW f n x) y <=
          edist x (f x) * Normal (k pow n) / Normal (1 - k)``;
