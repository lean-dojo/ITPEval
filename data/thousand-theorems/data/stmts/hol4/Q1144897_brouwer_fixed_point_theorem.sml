(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1144897, "Brouwer fixed-point theorem": every continuous self-map of a
  nonempty compact convex subset of a finite-dimensional real normed vector
  space has a fixed point in that subset. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory;
open topologyTheory;

val q1144897_real_normed_vector_space_def = new_definition (
  "q1144897_real_normed_vector_space_def",
  ``q1144897_real_normed_vector_space
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (norm : 'v -> real) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. 0 <= norm x) /\
      (!x. norm x = 0 <=> x = zero) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = abs a * norm x)``);

val q1144897_lincomb_def = new_definition (
  "q1144897_lincomb_def",
  ``q1144897_lincomb
      (zero : 'v) (add : 'v -> 'v -> 'v) (smul : real -> 'v -> 'v)
      (basis : 'v list) (coeff : num -> real) =
      FOLDL
        (\acc i. add acc (smul (coeff i) (EL i basis)))
        zero
        (GENLIST (\i. i) (LENGTH basis))``);

val q1144897_finite_dimensional_def = new_definition (
  "q1144897_finite_dimensional_def",
  ``q1144897_finite_dimensional
      (zero : 'v) (add : 'v -> 'v -> 'v) (smul : real -> 'v -> 'v) <=>
      ?basis : 'v list.
        !x : 'v.
          ?coeff : num -> real.
            q1144897_lincomb zero add smul basis coeff = x``);

val q1144897_open_def = new_definition (
  "q1144897_open_def",
  ``q1144897_open
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (u : 'v set) <=>
      !x. x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. norm (add y (neg x)) < epsilon ==> y IN u``);

val q1144897_compact_def = new_definition (
  "q1144897_compact_def",
  ``q1144897_compact
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (s : 'v set) <=>
      !cover : ('v set) set.
        (!u. u IN cover ==> q1144897_open add neg norm u) /\
        s SUBSET UNIONS cover
        ==>
        ?subcover.
          FINITE subcover /\
          subcover SUBSET cover /\
          s SUBSET UNIONS subcover``);

val q1144897_convex_def = new_definition (
  "q1144897_convex_def",
  ``q1144897_convex
      (add : 'v -> 'v -> 'v) (smul : real -> 'v -> 'v)
      (s : 'v set) <=>
      !x y t.
        x IN s /\ y IN s /\ 0 <= t /\ t <= 1
        ==>
        add (smul (1 - t) x) (smul t y) IN s``);

val q1144897_continuous_on_def = new_definition (
  "q1144897_continuous_on_def",
  ``q1144897_continuous_on
      (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (norm : 'v -> real) (s : 'v set) (f : 'v -> 'v) <=>
      !x.
        x IN s ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y.
              y IN s /\
              norm (add y (neg x)) < delta
              ==>
              norm (add (f y) (neg (f x))) < epsilon``);

val brouwer_fixed_point =
  ``!(zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (norm : 'v -> real)
      (s : 'v set) (f : 'v -> 'v).
      q1144897_real_normed_vector_space zero add neg smul norm /\
      q1144897_finite_dimensional zero add smul /\
      q1144897_convex add smul s /\
      q1144897_compact add neg norm s /\
      (?x. x IN s) /\
      q1144897_continuous_on add neg norm s f /\
      (!x. x IN s ==> f x IN s)
      ==>
      ?x. x IN s /\ f x = x``;
