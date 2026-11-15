(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527215 (thousand-theorems__hol4__Q3527215), "Hilbert projection theorem":
  every point in a real inner-product space has a nearest point in each
  nonempty complete convex subset. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val q3527215_real_inner_product_space_def = new_definition (
  "q3527215_real_inner_product_space_def",
  ``q3527215_real_inner_product_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (inner : 'e -> 'e -> real) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!x y. inner x y = inner y x) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!a x y. inner (smul a x) y = a * inner x y) /\
      (!x. 0 <= inner x x) /\
      (!x. (inner x x = 0) <=> (x = zero))``);

val q3527215_norm_def = new_definition (
  "q3527215_norm_def",
  ``q3527215_norm (inner : 'e -> 'e -> real) (x : 'e) =
      sqrt (inner x x)``);

val q3527215_sub_def = new_definition (
  "q3527215_sub_def",
  ``q3527215_sub
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) x y =
      add x (neg y)``);

val q3527215_cauchy_def = new_definition (
  "q3527215_cauchy_def",
  ``q3527215_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (inner : 'e -> 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          q3527215_norm inner
            (q3527215_sub add neg (u m) (u n)) < epsilon``);

val q3527215_tendsto_def = new_definition (
  "q3527215_tendsto_def",
  ``q3527215_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (inner : 'e -> 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==>
          q3527215_norm inner
            (q3527215_sub add neg (u n) x) < epsilon``);

val q3527215_complete_subset_def = new_definition (
  "q3527215_complete_subset_def",
  ``q3527215_complete_subset
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (inner : 'e -> 'e -> real) (s : 'e -> bool) <=>
      !u : num -> 'e.
        (!n. s (u n)) /\
        q3527215_cauchy add neg inner u
        ==>
        ?x : 'e.
          s x /\ q3527215_tendsto add neg inner u x``);

val q3527215_convex_def = new_definition (
  "q3527215_convex_def",
  ``q3527215_convex
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (s : 'e -> bool) <=>
      !x y a b.
        s x /\ s y /\ 0 <= a /\ 0 <= b /\ a + b = 1
        ==>
        s (add (smul a x) (smul b y))``);

val q3527215_distance_value_def = new_definition (
  "q3527215_distance_value_def",
  ``q3527215_distance_value
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (inner : 'e -> 'e -> real) (s : 'e -> bool)
      (u : 'e) (r : real) <=>
      ?w : 'e.
        s w /\
        r =
          q3527215_norm inner
            (q3527215_sub add neg u w)``);

val q3527215_is_infimum_def = new_definition (
  "q3527215_is_infimum_def",
  ``q3527215_is_infimum (P : real -> bool) (a : real) <=>
      (!r. P r ==> a <= r) /\
      (!b. (!r. P r ==> b <= r) ==> b <= a)``);

val exists_norm_eq_iInf_of_complete_convex =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (inner : 'e -> 'e -> real)
      (s : 'e -> bool).
      q3527215_real_inner_product_space zero add neg smul inner /\
      (?x : 'e. s x) /\
      q3527215_complete_subset add neg inner s /\
      q3527215_convex add smul s
      ==>
      !u : 'e.
        ?v : 'e.
          s v /\
          q3527215_is_infimum
            (q3527215_distance_value add neg inner s u)
            (q3527215_norm inner
              (q3527215_sub add neg u v))``;
