(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q720469, "Chevalley–Warning theorem": over a finite field, if the sum of
  the total degrees of a finite family of multivariate polynomials is less
  than the number of variables, then the field characteristic divides the
  number of their common zeros. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val q720469_field_def = new_definition (
  "q720469_field_def",
  ``q720469_field
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (invK : 'k -> 'k) <=>
      zero <> oneK /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul oneK x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      invK zero = zero /\
      (!x. x <> zero ==> mul (invK x) x = oneK)``);

val q720469_nat_cast_def = new_definition (
  "q720469_nat_cast_def",
  ``q720469_nat_cast
      (zero : 'k) (oneK : 'k) (add : 'k -> 'k -> 'k) (n : num) =
      FUNPOW (add oneK) n zero``);

val q720469_characteristic_def = new_definition (
  "q720469_characteristic_def",
  ``q720469_characteristic
      (zero : 'k) (oneK : 'k) (add : 'k -> 'k -> 'k) (p : num) <=>
      !n : num.
        (q720469_nat_cast zero oneK add n = zero <=> divides p n)``);

val q720469_polynomial_def = new_definition (
  "q720469_polynomial_def",
  ``q720469_polynomial
      (zero : 'k) (q : ('v -> num) -> 'k) <=>
      FINITE {m : 'v -> num | q m <> zero}``);

val q720469_monomial_degree_def = new_definition (
  "q720469_monomial_degree_def",
  ``q720469_monomial_degree (m : 'v -> num) =
      ITSET (\v acc. m v + acc) (UNIV : 'v set) 0``);

val q720469_total_degree_def = new_definition (
  "q720469_total_degree_def",
  ``q720469_total_degree
      (zero : 'k) (q : ('v -> num) -> 'k) =
      if (!m : 'v -> num. q m = zero)
      then 0
      else
        MAX_SET
          (IMAGE q720469_monomial_degree
            {m : 'v -> num | q m <> zero})``);

val q720469_monomial_value_def = new_definition (
  "q720469_monomial_value_def",
  ``q720469_monomial_value
      (oneK : 'k) (mul : 'k -> 'k -> 'k)
      (x : 'v -> 'k) (m : 'v -> num) =
      ITSET
        (\v acc. mul (FUNPOW (mul (x v)) (m v) oneK) acc)
        (UNIV : 'v set)
        oneK``);

val q720469_eval_def = new_definition (
  "q720469_eval_def",
  ``q720469_eval
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (x : 'v -> 'k) (q : ('v -> num) -> 'k) =
      ITSET
        (\m acc.
          add
            (mul (q m) (q720469_monomial_value oneK mul x m))
            acc)
        {m : 'v -> num | q m <> zero}
        zero``);

val q720469_sum_degrees_def = new_definition (
  "q720469_sum_degrees_def",
  ``q720469_sum_degrees
      (zero : 'k) (s : 'i set)
      (f : 'i -> ('v -> num) -> 'k) =
      ITSET
        (\i acc. q720469_total_degree zero (f i) + acc)
        s
        0``);

val char_dvd_card_solutions_of_sum_lt =
  ``!(zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (invK : 'k -> 'k)
      (p : num) (s : 'i set)
      (f : 'i -> ('v -> num) -> 'k).
      q720469_field zero oneK add mul neg invK /\
      FINITE (UNIV : 'k set) /\
      FINITE (UNIV : 'v set) /\
      q720469_characteristic zero oneK add p /\
      FINITE s /\
      (!i : 'i. q720469_polynomial zero (f i)) /\
      q720469_sum_degrees zero s f < CARD (UNIV : 'v set)
      ==>
      divides p
        (CARD
          {x : 'v -> 'k |
             !i : 'i.
               i IN s ==>
               q720469_eval zero oneK add mul x (f i) = zero})``;
