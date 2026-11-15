(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q7433182, "Schwartz-Zippel theorem": the sharp Schwartz-Zippel bound for a
  nonzero multivariate polynomial over an integral domain, evaluated on a
  dependent product of finite subsets. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory ratTheory;

val q7433182_integral_domain_def = new_definition (
  "q7433182_integral_domain_def",
  ``q7433182_integral_domain
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) <=>
      zero <> oneR /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul oneR x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      (!x y. mul x y = zero ==> x = zero \/ y = zero)``);

val q7433182_polynomial_def = new_definition (
  "q7433182_polynomial_def",
  ``q7433182_polynomial
      (zero : 'r) (n : num) (p : (num -> num) -> 'r) <=>
      FINITE {m : num -> num | p m <> zero} /\
      (!m : num -> num.
         p m <> zero ==> !i : num. n <= i ==> m i = 0)``);

val q7433182_monomial_value_def = new_definition (
  "q7433182_monomial_value_def",
  ``q7433182_monomial_value
      (oneR : 'r) (mul : 'r -> 'r -> 'r)
      (n : num) (x : num -> 'r) (m : num -> num) =
      ITSET
        (\i acc. mul (FUNPOW (mul (x i)) (m i) oneR) acc)
        (count n)
        oneR``);

val q7433182_eval_def = new_definition (
  "q7433182_eval_def",
  ``q7433182_eval
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (n : num) (x : num -> 'r) (p : (num -> num) -> 'r) =
      ITSET
        (\m acc.
           add
             (mul (p m)
               (q7433182_monomial_value oneR mul n x m))
             acc)
        {m : num -> num | p m <> zero}
        zero``);

val q7433182_grid_point_def = new_definition (
  "q7433182_grid_point_def",
  ``q7433182_grid_point
      (zero : 'r) (n : num) (sets : num -> 'r set) (x : num -> 'r) <=>
      (!i : num. i < n ==> x i IN sets i) /\
      (!i : num. n <= i ==> x i = zero)``);

val q7433182_card_product_def = new_definition (
  "q7433182_card_product_def",
  ``q7433182_card_product (n : num) (sets : num -> 'r set) =
      ITSET (\i acc. CARD (sets i) * acc) (count n) 1``);

val q7433182_safe_div_def = new_definition (
  "q7433182_safe_div_def",
  ``q7433182_safe_div (a : rat) (b : rat) =
      if b = 0q then 0q else a / b``);

val q7433182_monomial_weight_def = new_definition (
  "q7433182_monomial_weight_def",
  ``q7433182_monomial_weight
      (n : num) (sets : num -> 'r set) (m : num -> num) =
      ITSET
        (\i acc.
           rat_add
             (q7433182_safe_div
               (rat_of_num (m i))
               (rat_of_num (CARD (sets i))))
             acc)
        (count n)
        0q``);

val MvPolynomial_schwartz_zippel_sup_sum =
  ``!(zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r)
      (n : num) (p : (num -> num) -> 'r)
      (sets : num -> 'r set).
      q7433182_integral_domain zero oneR add mul neg /\
      q7433182_polynomial zero n p /\
      p <> (\m : num -> num. zero) /\
      (!i : num. i < n ==> FINITE (sets i))
      ==>
      ?m : num -> num.
        p m <> zero /\
        q7433182_safe_div
          (rat_of_num
            (CARD
              {x : num -> 'r |
                 q7433182_grid_point zero n sets x /\
                 q7433182_eval zero oneR add mul n x p = zero}))
          (rat_of_num (q7433182_card_product n sets)) <=
        q7433182_monomial_weight n sets m``;
