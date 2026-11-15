(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1357684 (thousand-theorems__hol4__Q1357684), "Riesz representation
  theorem": inner product with a vector gives a conjugate-linear isometric
  equivalence from a real or complex Hilbert space to its continuous dual.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory complexTheory;

val q1357684_add_comm_group_def = new_definition (
  "q1357684_add_comm_group_def",
  ``q1357684_add_comm_group
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero)``);

val q1357684_real_module_def = new_definition (
  "q1357684_real_module_def",
  ``q1357684_real_module
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : real -> 'e -> 'e) <=>
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero)``);

val q1357684_complex_module_def = new_definition (
  "q1357684_complex_module_def",
  ``q1357684_complex_module
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : complex -> 'e -> 'e) <=>
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero)``);

val q1357684_real_inner_product_def = new_definition (
  "q1357684_real_inner_product_def",
  ``q1357684_real_inner_product
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : real -> 'e -> 'e) (inner : 'e -> 'e -> real) <=>
      (!x y. inner x y = inner y x) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!a x y. inner (smul a x) y = a * inner x y) /\
      (!x. 0 <= inner x x) /\
      (!x. (inner x x = 0) <=> (x = zero))``);

val q1357684_complex_inner_product_def = new_definition (
  "q1357684_complex_inner_product_def",
  ``q1357684_complex_inner_product
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : complex -> 'e -> 'e)
      (inner : 'e -> 'e -> complex) <=>
      (!x y. inner x y = conj (inner y x)) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!a x y. inner (smul a x) y = conj a * inner x y) /\
      (!x. 0 <= RE (inner x x)) /\
      (!x. IM (inner x x) = 0) /\
      (!x. (inner x x = 0) <=> (x = zero))``);

val q1357684_real_norm_def = new_definition (
  "q1357684_real_norm_def",
  ``q1357684_real_norm (inner : 'e -> 'e -> real) (x : 'e) =
      sqrt (inner x x)``);

val q1357684_complex_norm_def = new_definition (
  "q1357684_complex_norm_def",
  ``q1357684_complex_norm
      (inner : 'e -> 'e -> complex) (x : 'e) =
      sqrt (RE (inner x x))``);

val q1357684_cauchy_def = new_definition (
  "q1357684_cauchy_def",
  ``q1357684_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q1357684_tendsto_def = new_definition (
  "q1357684_tendsto_def",
  ``q1357684_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q1357684_complete_def = new_definition (
  "q1357684_complete_def",
  ``q1357684_complete
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      !u : num -> 'e.
        q1357684_cauchy add neg norm u ==>
        ?x : 'e. q1357684_tendsto add neg norm u x``);

val q1357684_real_continuous_linear_functional_def = new_definition (
  "q1357684_real_continuous_linear_functional_def",
  ``q1357684_real_continuous_linear_functional
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (norm : 'e -> real) (ell : 'e -> real) <=>
      (!x y. ell (add x y) = ell x + ell y) /\
      (!a x. ell (smul a x) = a * ell x) /\
      ?K : real.
        0 <= K /\ !x. abs (ell x) <= K * norm x``);

val q1357684_complex_continuous_linear_functional_def = new_definition (
  "q1357684_complex_continuous_linear_functional_def",
  ``q1357684_complex_continuous_linear_functional
      (add : 'e -> 'e -> 'e) (smul : complex -> 'e -> 'e)
      (norm : 'e -> real) (ell : 'e -> complex) <=>
      (!x y. ell (add x y) = ell x + ell y) /\
      (!a x. ell (smul a x) = a * ell x) /\
      ?K : real.
        0 <= K /\ !x. modu (ell x) <= K * norm x``);

val q1357684_real_has_dual_norm_def = new_definition (
  "q1357684_real_has_dual_norm_def",
  ``q1357684_real_has_dual_norm
      (inner : 'e -> 'e -> real) (ell : 'e -> real) (r : real) <=>
      0 <= r /\
      (!x. abs (ell x) <= r * q1357684_real_norm inner x) /\
      (!K : real.
        0 <= K /\
        (!x. abs (ell x) <= K * q1357684_real_norm inner x)
        ==>
        r <= K)``);

val q1357684_complex_has_dual_norm_def = new_definition (
  "q1357684_complex_has_dual_norm_def",
  ``q1357684_complex_has_dual_norm
      (inner : 'e -> 'e -> complex) (ell : 'e -> complex) (r : real) <=>
      0 <= r /\
      (!x. modu (ell x) <= r * q1357684_complex_norm inner x) /\
      (!K : real.
        0 <= K /\
        (!x. modu (ell x) <= K * q1357684_complex_norm inner x)
        ==>
        r <= K)``);

val InnerProductSpace_toDual_real =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (inner : 'e -> 'e -> real).
      q1357684_add_comm_group zero add neg /\
      q1357684_real_module zero add smul /\
      q1357684_real_inner_product zero add smul inner /\
      q1357684_complete add neg (q1357684_real_norm inner)
      ==>
      ?to_dual : 'e -> 'e -> real.
      ?from_dual : ('e -> real) -> 'e.
        (!x y. to_dual x y = inner x y) /\
        (!x.
          q1357684_real_continuous_linear_functional
            add smul (q1357684_real_norm inner) (to_dual x)) /\
        (!x.
          q1357684_real_has_dual_norm
            inner (to_dual x) (q1357684_real_norm inner x)) /\
        (!x. from_dual (to_dual x) = x) /\
        (!ell : 'e -> real.
          q1357684_real_continuous_linear_functional
            add smul (q1357684_real_norm inner) ell
          ==>
          to_dual (from_dual ell) = ell)``;

val InnerProductSpace_toDual_complex =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e)
      (inner : 'e -> 'e -> complex).
      q1357684_add_comm_group zero add neg /\
      q1357684_complex_module zero add smul /\
      q1357684_complex_inner_product zero add smul inner /\
      q1357684_complete add neg (q1357684_complex_norm inner)
      ==>
      ?to_dual : 'e -> 'e -> complex.
      ?from_dual : ('e -> complex) -> 'e.
        (!x y. to_dual x y = inner x y) /\
        (!x.
          q1357684_complex_continuous_linear_functional
            add smul (q1357684_complex_norm inner) (to_dual x)) /\
        (!x.
          q1357684_complex_has_dual_norm
            inner (to_dual x) (q1357684_complex_norm inner x)) /\
        (!x. from_dual (to_dual x) = x) /\
        (!ell : 'e -> complex.
          q1357684_complex_continuous_linear_functional
            add smul (q1357684_complex_norm inner) ell
          ==>
          to_dual (from_dual ell) = ell)``;
