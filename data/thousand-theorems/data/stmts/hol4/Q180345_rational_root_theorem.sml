(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q180345, "Rational root theorem": over a unique factorization domain, the
  reduced numerator and denominator of a root in its fraction field divide,
  respectively, the polynomial's constant and leading coefficients. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val q180345_integral_domain_def = new_definition (
  "q180345_integral_domain_def",
  ``q180345_integral_domain
      (zero : 'a) (one : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) <=>
      zero <> one /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul one x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      (!x y. mul x y = zero ==> x = zero \/ y = zero)``);

val q180345_divides_def = new_definition (
  "q180345_divides_def",
  ``q180345_divides (mul : 'a -> 'a -> 'a) (a : 'a) b <=>
      ?c : 'a. mul a c = b``);

val q180345_unit_def = new_definition (
  "q180345_unit_def",
  ``q180345_unit (one : 'a) (mul : 'a -> 'a -> 'a) (u : 'a) <=>
      ?v : 'a. mul u v = one``);

val q180345_irreducible_def = new_definition (
  "q180345_irreducible_def",
  ``q180345_irreducible
      (zero : 'a) (one : 'a) (mul : 'a -> 'a -> 'a) (q : 'a) <=>
      q <> zero /\
      ~q180345_unit one mul q /\
      !a b : 'a.
        mul a b = q ==>
        q180345_unit one mul a \/ q180345_unit one mul b``);

val q180345_prime_def = new_definition (
  "q180345_prime_def",
  ``q180345_prime
      (zero : 'a) (one : 'a) (mul : 'a -> 'a -> 'a) (q : 'a) <=>
      q <> zero /\
      ~q180345_unit one mul q /\
      !a b : 'a.
        q180345_divides mul q (mul a b) ==>
        q180345_divides mul q a \/ q180345_divides mul q b``);

val q180345_ufd_def = new_definition (
  "q180345_ufd_def",
  ``q180345_ufd
      (zero : 'a) (one : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) <=>
      q180345_integral_domain zero one add mul neg /\
      (!q : 'a.
         q180345_irreducible zero one mul q ==>
         q180345_prime zero one mul q) /\
      (!x : 'a.
         x <> zero ==>
         ?u : 'a. ?factors : 'a list.
           q180345_unit one mul u /\
           EVERY (q180345_irreducible zero one mul) factors /\
           x = mul u (FOLDL mul one factors))``);

val q180345_field_def = new_definition (
  "q180345_field_def",
  ``q180345_field
      (zero : 'k) (one : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (inv : 'k -> 'k) <=>
      zero <> one /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul one x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      (!x. x <> zero ==> mul (inv x) x = one)``);

val q180345_fraction_context_def = new_definition (
  "q180345_fraction_context_def",
  ``q180345_fraction_context
      (Azero : 'a) (Aone : 'a)
      (Aadd : 'a -> 'a -> 'a) (Amul : 'a -> 'a -> 'a)
      (Aneg : 'a -> 'a)
      (Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (Kneg : 'k -> 'k) (Kinv : 'k -> 'k)
      (embed : 'a -> 'k) (num : 'k -> 'a) (den : 'k -> 'a) <=>
      q180345_field Kzero Kone Kadd Kmul Kneg Kinv /\
      embed Azero = Kzero /\
      embed Aone = Kone /\
      (!x y. embed (Aadd x y) = Kadd (embed x) (embed y)) /\
      (!x y. embed (Amul x y) = Kmul (embed x) (embed y)) /\
      (!x. embed (Aneg x) = Kneg (embed x)) /\
      (!x y. embed x = embed y ==> x = y) /\
      (!r : 'k.
         den r <> Azero /\
         Kmul r (embed (den r)) = embed (num r) /\
         !c : 'a.
           q180345_divides Amul c (num r) /\
           q180345_divides Amul c (den r)
           ==>
           q180345_unit Aone Amul c)``);

val q180345_polynomial_def = new_definition (
  "q180345_polynomial_def",
  ``q180345_polynomial (zero : 'a) (p : num -> 'a) <=>
      FINITE {n : num | p n <> zero}``);

val q180345_nat_degree_def = new_definition (
  "q180345_nat_degree_def",
  ``q180345_nat_degree (zero : 'a) (p : num -> 'a) =
      if (!n : num. p n = zero)
      then 0
      else MAX_SET {n : num | p n <> zero}``);

val q180345_leading_coeff_def = new_definition (
  "q180345_leading_coeff_def",
  ``q180345_leading_coeff (zero : 'a) (p : num -> 'a) =
      p (q180345_nat_degree zero p)``);

val q180345_poly_eval_def = new_definition (
  "q180345_poly_eval_def",
  ``q180345_poly_eval
      (Azero : 'a) (Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (embed : 'a -> 'k) (p : num -> 'a) (r : 'k) =
      ITSET
        (\n acc.
           Kadd
             (Kmul (embed (p n)) (FUNPOW (Kmul r) n Kone))
             acc)
        {n : num | p n <> Azero}
        Kzero``);

val num_dvd_of_is_root =
  ``!(Azero : 'a) (Aone : 'a)
      (Aadd : 'a -> 'a -> 'a) (Amul : 'a -> 'a -> 'a)
      (Aneg : 'a -> 'a)
      (Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (Kneg : 'k -> 'k) (Kinv : 'k -> 'k)
      (embed : 'a -> 'k) (num : 'k -> 'a) (den : 'k -> 'a)
      (p : num -> 'a) (r : 'k).
      q180345_ufd Azero Aone Aadd Amul Aneg /\
      q180345_fraction_context
        Azero Aone Aadd Amul Aneg
        Kzero Kone Kadd Kmul Kneg Kinv embed num den /\
      q180345_polynomial Azero p /\
      q180345_poly_eval Azero Kzero Kone Kadd Kmul embed p r = Kzero
      ==>
      q180345_divides Amul (num r) (p 0)``;

val den_dvd_of_is_root =
  ``!(Azero : 'a) (Aone : 'a)
      (Aadd : 'a -> 'a -> 'a) (Amul : 'a -> 'a -> 'a)
      (Aneg : 'a -> 'a)
      (Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (Kneg : 'k -> 'k) (Kinv : 'k -> 'k)
      (embed : 'a -> 'k) (num : 'k -> 'a) (den : 'k -> 'a)
      (p : num -> 'a) (r : 'k).
      q180345_ufd Azero Aone Aadd Amul Aneg /\
      q180345_fraction_context
        Azero Aone Aadd Amul Aneg
        Kzero Kone Kadd Kmul Kneg Kinv embed num den /\
      q180345_polynomial Azero p /\
      q180345_poly_eval Azero Kzero Kone Kadd Kmul embed p r = Kzero
      ==>
      q180345_divides
        Amul (den r) (q180345_leading_coeff Azero p)``;
