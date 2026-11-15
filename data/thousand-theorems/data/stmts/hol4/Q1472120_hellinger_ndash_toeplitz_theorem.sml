(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1472120 (thousand-theorems__hol4__Q1472120),
  "Hellinger&ndash;Toeplitz theorem": a symmetric linear operator on a
  complete real or complex inner product space is continuous. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory complexTheory;

val q1472120_rclike_def = new_definition (
  "q1472120_rclike_def",
  ``q1472120_rclike
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (conjK : 'k -> 'k) (reK : 'k -> real) <=>
      (?encodeR : 'k -> real. ?decodeR : real -> 'k.
        (!a. decodeR (encodeR a) = a) /\
        (!r. encodeR (decodeR r) = r) /\
        encodeR zeroK = 0 /\
        encodeR oneK = 1 /\
        (!a b. encodeR (addK a b) = encodeR a + encodeR b) /\
        (!a b. encodeR (mulK a b) = encodeR a * encodeR b) /\
        (!a. encodeR (conjK a) = encodeR a) /\
        (!a. reK a = encodeR a)) \/
      (?encodeC : 'k -> complex. ?decodeC : complex -> 'k.
        (!a. decodeC (encodeC a) = a) /\
        (!z. encodeC (decodeC z) = z) /\
        encodeC zeroK = 0 /\
        encodeC oneK = 1 /\
        (!a b. encodeC (addK a b) = encodeC a + encodeC b) /\
        (!a b. encodeC (mulK a b) = encodeC a * encodeC b) /\
        (!a. encodeC (conjK a) = conj (encodeC a)) /\
        (!a. reK a = RE (encodeC a)))``);

val q1472120_add_comm_group_def = new_definition (
  "q1472120_add_comm_group_def",
  ``q1472120_add_comm_group
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero)``);

val q1472120_module_def = new_definition (
  "q1472120_module_def",
  ``q1472120_module
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (add : 'e -> 'e -> 'e) (smul : 'k -> 'e -> 'e) <=>
      (!x. smul oneK x = x) /\
      (!a b x. smul (mulK a b) x = smul a (smul b x)) /\
      (!a b x. smul (addK a b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y))``);

val q1472120_inner_product_def = new_definition (
  "q1472120_inner_product_def",
  ``q1472120_inner_product
      (zeroK : 'k) (addK : 'k -> 'k -> 'k)
      (mulK : 'k -> 'k -> 'k)
      (conjK : 'k -> 'k) (reK : 'k -> real)
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : 'k -> 'e -> 'e) (inner : 'e -> 'e -> 'k) <=>
      (!x y. inner x y = conjK (inner y x)) /\
      (!x y z. inner (add x y) z = addK (inner x z) (inner y z)) /\
      (!a x y. inner (smul a x) y = mulK (conjK a) (inner x y)) /\
      (!x. 0 <= reK (inner x x)) /\
      (!x. (inner x x = zeroK) <=> (x = zero))``);

val q1472120_norm_def = new_definition (
  "q1472120_norm_def",
  ``q1472120_norm
      (reK : 'k -> real) (inner : 'e -> 'e -> 'k) (x : 'e) =
      sqrt (reK (inner x x))``);

val q1472120_cauchy_def = new_definition (
  "q1472120_cauchy_def",
  ``q1472120_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q1472120_tendsto_def = new_definition (
  "q1472120_tendsto_def",
  ``q1472120_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q1472120_complete_def = new_definition (
  "q1472120_complete_def",
  ``q1472120_complete
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      !u : num -> 'e.
        q1472120_cauchy add neg norm u ==>
        ?x : 'e. q1472120_tendsto add neg norm u x``);

val q1472120_linear_map_def = new_definition (
  "q1472120_linear_map_def",
  ``q1472120_linear_map
      (add : 'e -> 'e -> 'e) (smul : 'k -> 'e -> 'e)
      (t : 'e -> 'e) <=>
      (!x y. t (add x y) = add (t x) (t y)) /\
      (!a x. t (smul a x) = smul a (t x))``);

val q1472120_symmetric_def = new_definition (
  "q1472120_symmetric_def",
  ``q1472120_symmetric
      (inner : 'e -> 'e -> 'k) (t : 'e -> 'e) <=>
      !x y. inner (t x) y = inner x (t y)``);

val q1472120_continuous_def = new_definition (
  "q1472120_continuous_def",
  ``q1472120_continuous
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (t : 'e -> 'e) <=>
      !x : 'e. !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y : 'e.
            norm (add y (neg x)) < delta ==>
            norm (add (t y) (neg (t x))) < epsilon``);

val LinearMap_IsSymmetric_continuous =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (conjK : 'k -> 'k) (reK : 'k -> real)
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : 'k -> 'e -> 'e) (inner : 'e -> 'e -> 'k)
      (t : 'e -> 'e).
      q1472120_rclike zeroK oneK addK mulK conjK reK /\
      q1472120_add_comm_group zero add neg /\
      q1472120_module zeroK oneK addK mulK add smul /\
      q1472120_inner_product
        zeroK addK mulK conjK reK zero add smul inner /\
      q1472120_complete add neg (q1472120_norm reK inner) /\
      q1472120_linear_map add smul t /\
      q1472120_symmetric inner t
      ==>
      q1472120_continuous add neg (q1472120_norm reK inner) t``;
