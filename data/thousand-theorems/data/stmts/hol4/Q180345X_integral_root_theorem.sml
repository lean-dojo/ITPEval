(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q180345X, "Integral root theorem": a root in the fraction field of a unique
  factorization domain of a monic polynomial over that domain is the image of
  an element of the domain. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val q180345x_integral_domain_def = new_definition (
  "q180345x_integral_domain_def",
  ``q180345x_integral_domain
      (zeroA : 'a) (oneA : 'a)
      (addA : 'a -> 'a -> 'a) (mulA : 'a -> 'a -> 'a)
      (negA : 'a -> 'a) <=>
      zeroA <> oneA /\
      (!x y z. addA (addA x y) z = addA x (addA y z)) /\
      (!x y. addA x y = addA y x) /\
      (!x. addA zeroA x = x) /\
      (!x. addA (negA x) x = zeroA) /\
      (!x y z. mulA (mulA x y) z = mulA x (mulA y z)) /\
      (!x y. mulA x y = mulA y x) /\
      (!x. mulA oneA x = x) /\
      (!x y z. mulA x (addA y z) = addA (mulA x y) (mulA x z)) /\
      (!x y. mulA x y = zeroA ==> x = zeroA \/ y = zeroA)``);

val q180345x_divides_def = new_definition (
  "q180345x_divides_def",
  ``q180345x_divides (mulA : 'a -> 'a -> 'a) (a : 'a) b <=>
      ?c : 'a. mulA a c = b``);

val q180345x_unit_def = new_definition (
  "q180345x_unit_def",
  ``q180345x_unit (oneA : 'a) (mulA : 'a -> 'a -> 'a) (u : 'a) <=>
      ?v : 'a. mulA u v = oneA``);

val q180345x_irreducible_def = new_definition (
  "q180345x_irreducible_def",
  ``q180345x_irreducible
      (zeroA : 'a) (oneA : 'a) (mulA : 'a -> 'a -> 'a) (q : 'a) <=>
      q <> zeroA /\
      ~q180345x_unit oneA mulA q /\
      !a b : 'a.
        mulA a b = q ==>
        q180345x_unit oneA mulA a \/ q180345x_unit oneA mulA b``);

val q180345x_prime_def = new_definition (
  "q180345x_prime_def",
  ``q180345x_prime
      (zeroA : 'a) (oneA : 'a) (mulA : 'a -> 'a -> 'a) (q : 'a) <=>
      q <> zeroA /\
      ~q180345x_unit oneA mulA q /\
      !a b : 'a.
        q180345x_divides mulA q (mulA a b) ==>
        q180345x_divides mulA q a \/ q180345x_divides mulA q b``);

val q180345x_ufd_def = new_definition (
  "q180345x_ufd_def",
  ``q180345x_ufd
      (zeroA : 'a) (oneA : 'a)
      (addA : 'a -> 'a -> 'a) (mulA : 'a -> 'a -> 'a)
      (negA : 'a -> 'a) <=>
      q180345x_integral_domain zeroA oneA addA mulA negA /\
      (!q : 'a.
         q180345x_irreducible zeroA oneA mulA q ==>
         q180345x_prime zeroA oneA mulA q) /\
      (!x : 'a.
         x <> zeroA ==>
         ?u : 'a. ?factors : 'a list.
           q180345x_unit oneA mulA u /\
           EVERY (q180345x_irreducible zeroA oneA mulA) factors /\
           x = mulA u (FOLDL mulA oneA factors))``);

val q180345x_field_def = new_definition (
  "q180345x_field_def",
  ``q180345x_field
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k) <=>
      zeroK <> oneK /\
      (!x y z. addK (addK x y) z = addK x (addK y z)) /\
      (!x y. addK x y = addK y x) /\
      (!x. addK zeroK x = x) /\
      (!x. addK (negK x) x = zeroK) /\
      (!x y z. mulK (mulK x y) z = mulK x (mulK y z)) /\
      (!x y. mulK x y = mulK y x) /\
      (!x. mulK oneK x = x) /\
      (!x y z. mulK x (addK y z) = addK (mulK x y) (mulK x z)) /\
      (!x. x <> zeroK ==> mulK (invK x) x = oneK)``);

val q180345x_fraction_field_def = new_definition (
  "q180345x_fraction_field_def",
  ``q180345x_fraction_field
      (Azero : 'a) (Aone : 'a)
      (Aadd : 'a -> 'a -> 'a) (Amul : 'a -> 'a -> 'a)
      (Aneg : 'a -> 'a)
      (Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (Kneg : 'k -> 'k) (Kinv : 'k -> 'k)
      (embed : 'a -> 'k) <=>
      q180345x_field Kzero Kone Kadd Kmul Kneg Kinv /\
      embed Azero = Kzero /\
      embed Aone = Kone /\
      (!x y. embed (Aadd x y) = Kadd (embed x) (embed y)) /\
      (!x y. embed (Amul x y) = Kmul (embed x) (embed y)) /\
      (!x. embed (Aneg x) = Kneg (embed x)) /\
      (!x y. embed x = embed y ==> x = y) /\
      (!r : 'k.
         ?a b : 'a.
           b <> Azero /\
           Kmul r (embed b) = embed a)``);

val q180345x_polynomial_def = new_definition (
  "q180345x_polynomial_def",
  ``q180345x_polynomial (zero : 'a) (p : num -> 'a) <=>
      FINITE {n : num | p n <> zero}``);

val q180345x_nat_degree_def = new_definition (
  "q180345x_nat_degree_def",
  ``q180345x_nat_degree (zero : 'a) (p : num -> 'a) =
      if (!n : num. p n = zero)
      then 0
      else MAX_SET {n : num | p n <> zero}``);

val q180345x_leading_coeff_def = new_definition (
  "q180345x_leading_coeff_def",
  ``q180345x_leading_coeff (zero : 'a) (p : num -> 'a) =
      p (q180345x_nat_degree zero p)``);

val q180345x_poly_eval_def = new_definition (
  "q180345x_poly_eval_def",
  ``q180345x_poly_eval
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

val isInteger_of_is_root_of_monic =
  ``!(Azero : 'a) (Aone : 'a)
      (Aadd : 'a -> 'a -> 'a) (Amul : 'a -> 'a -> 'a)
      (Aneg : 'a -> 'a)
      (Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (Kneg : 'k -> 'k) (Kinv : 'k -> 'k)
      (embed : 'a -> 'k) (p : num -> 'a) (r : 'k).
      q180345x_ufd Azero Aone Aadd Amul Aneg /\
      q180345x_fraction_field
        Azero Aone Aadd Amul Aneg
        Kzero Kone Kadd Kmul Kneg Kinv embed /\
      q180345x_polynomial Azero p /\
      q180345x_leading_coeff Azero p = Aone /\
      q180345x_poly_eval
        Azero Kzero Kone Kadd Kmul embed p r = Kzero
      ==>
      ?a : 'a. r = embed a``;
