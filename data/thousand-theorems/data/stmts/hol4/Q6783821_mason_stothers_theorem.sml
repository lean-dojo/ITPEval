(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q6783821, "Mason–Stothers theorem": for nonzero polynomials a, b, c over an
  arbitrary field, with a and b coprime and a + b + c = 0, each natural degree
  plus one is bounded by the natural degree of the radical of abc, or all
  three formal derivatives vanish. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q6783821_field_def = new_definition (
  "q6783821_field_def",
  ``q6783821_field
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (invK : 'k -> 'k) <=>
      zero <> oneK /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul oneK x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      (!x. x <> zero ==> mul (invK x) x = oneK)``);

val q6783821_polynomial_def = new_definition (
  "q6783821_polynomial_def",
  ``q6783821_polynomial (zero : 'k) (p : num -> 'k) <=>
      FINITE {n : num | p n <> zero}``);

val q6783821_poly_zero_def = new_definition (
  "q6783821_poly_zero_def",
  ``q6783821_poly_zero (zero : 'k) = (\n : num. zero)``);

val q6783821_poly_one_def = new_definition (
  "q6783821_poly_one_def",
  ``q6783821_poly_one (zero : 'k) (oneK : 'k) =
      (\n : num. if n = 0 then oneK else zero)``);

val q6783821_poly_add_def = new_definition (
  "q6783821_poly_add_def",
  ``q6783821_poly_add
      (add : 'k -> 'k -> 'k) (p : num -> 'k) q =
      (\n. add (p n) (q n))``);

val q6783821_poly_mul_def = new_definition (
  "q6783821_poly_mul_def",
  ``q6783821_poly_mul
      (zero : 'k) (add : 'k -> 'k -> 'k)
      (mul : 'k -> 'k -> 'k)
      (p : num -> 'k) (q : num -> 'k) (n : num) =
      ITSET
        (\i acc. add (mul (p i) (q (n - i))) acc)
        (count (SUC n))
        zero``);

val q6783821_nat_degree_def = new_definition (
  "q6783821_nat_degree_def",
  ``q6783821_nat_degree (zero : 'k) (p : num -> 'k) =
      if (!n : num. p n = zero)
      then 0
      else MAX_SET {n : num | p n <> zero}``);

val q6783821_nat_cast_def = new_definition (
  "q6783821_nat_cast_def",
  ``q6783821_nat_cast
      (zero : 'k) (oneK : 'k) (add : 'k -> 'k -> 'k) (n : num) =
      FUNPOW (add oneK) n zero``);

val q6783821_derivative_def = new_definition (
  "q6783821_derivative_def",
  ``q6783821_derivative
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (p : num -> 'k) =
      (\n : num.
         mul
           (q6783821_nat_cast zero oneK add (SUC n))
           (p (SUC n)))``);

val q6783821_divides_def = new_definition (
  "q6783821_divides_def",
  ``q6783821_divides
      (zero : 'k) (add : 'k -> 'k -> 'k)
      (mul : 'k -> 'k -> 'k)
      (p : num -> 'k) (q : num -> 'k) <=>
      ?r : num -> 'k.
        q6783821_polynomial zero r /\
        q = q6783821_poly_mul zero add mul p r``);

val q6783821_unit_def = new_definition (
  "q6783821_unit_def",
  ``q6783821_unit
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (p : num -> 'k) <=>
      q6783821_divides zero add mul p
        (q6783821_poly_one zero oneK)``);

val q6783821_squarefree_def = new_definition (
  "q6783821_squarefree_def",
  ``q6783821_squarefree
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (p : num -> 'k) <=>
      q6783821_polynomial zero p /\
      !q : num -> 'k.
        q6783821_polynomial zero q /\
        q6783821_divides zero add mul
          (q6783821_poly_mul zero add mul q q) p
        ==>
        q6783821_unit zero oneK add mul q``);

val q6783821_radical_nat_degree_def = new_definition (
  "q6783821_radical_nat_degree_def",
  ``q6783821_radical_nat_degree
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (p : num -> 'k) =
      MAX_SET
        {d : num |
          ?r : num -> 'k.
            q6783821_squarefree zero oneK add mul r /\
            q6783821_divides zero add mul r p /\
            d = q6783821_nat_degree zero r}``);

val q6783821_coprime_def = new_definition (
  "q6783821_coprime_def",
  ``q6783821_coprime
      (zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (p : num -> 'k) (q : num -> 'k) <=>
      ?x : num -> 'k. ?y : num -> 'k.
        q6783821_polynomial zero x /\
        q6783821_polynomial zero y /\
        q6783821_poly_add add
          (q6783821_poly_mul zero add mul x p)
          (q6783821_poly_mul zero add mul y q) =
        q6783821_poly_one zero oneK``);

val Polynomial_abc =
  ``!(zero : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (invK : 'k -> 'k)
      (a : num -> 'k) (b : num -> 'k) (c : num -> 'k).
      q6783821_field zero oneK add mul neg invK /\
      q6783821_polynomial zero a /\
      q6783821_polynomial zero b /\
      q6783821_polynomial zero c /\
      a <> q6783821_poly_zero zero /\
      b <> q6783821_poly_zero zero /\
      c <> q6783821_poly_zero zero /\
      q6783821_coprime zero oneK add mul a b /\
      q6783821_poly_add add
        (q6783821_poly_add add a b) c =
        q6783821_poly_zero zero
      ==>
      let abc =
        q6783821_poly_mul zero add mul
          (q6783821_poly_mul zero add mul a b) c
      in
      let radical_degree =
        q6783821_radical_nat_degree zero oneK add mul abc
      in
        (q6783821_nat_degree zero a + 1 <= radical_degree /\
         q6783821_nat_degree zero b + 1 <= radical_degree /\
         q6783821_nat_degree zero c + 1 <= radical_degree) \/
        (q6783821_derivative zero oneK add mul a =
           q6783821_poly_zero zero /\
         q6783821_derivative zero oneK add mul b =
           q6783821_poly_zero zero /\
         q6783821_derivative zero oneK add mul c =
           q6783821_poly_zero zero)``;
