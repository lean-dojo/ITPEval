(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q656645, "Hilbert's basis theorem": the univariate polynomial ring over a
  commutative Noetherian ring is Noetherian. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val q656645_comm_ring_def = new_definition (
  "q656645_comm_ring_def",
  ``q656645_comm_ring
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul oneR x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z))``);

val q656645_ideal_def = new_definition (
  "q656645_ideal_def",
  ``q656645_ideal
      (carrier : 'a -> bool)
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (mul : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (ideal : 'a set) <=>
      (!x. x IN ideal ==> carrier x) /\
      zero IN ideal /\
      (!x y. x IN ideal /\ y IN ideal ==> add x y IN ideal) /\
      (!x. x IN ideal ==> neg x IN ideal) /\
      (!a x. carrier a /\ x IN ideal ==> mul a x IN ideal)``);

val q656645_span_def = new_definition (
  "q656645_span_def",
  ``q656645_span
      (carrier : 'a -> bool)
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (mul : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (s : 'a set) =
      {x |
        carrier x /\
        !other : 'a set.
          q656645_ideal carrier zero add mul neg other /\
          s SUBSET other
          ==>
          x IN other}``);

val q656645_noetherian_def = new_definition (
  "q656645_noetherian_def",
  ``q656645_noetherian
      (carrier : 'a -> bool)
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (mul : 'a -> 'a -> 'a) (neg : 'a -> 'a) <=>
      !ideal : 'a set.
        q656645_ideal carrier zero add mul neg ideal
        ==>
        ?s : 'a set.
          FINITE s /\
          s SUBSET ideal /\
          q656645_span carrier zero add mul neg s = ideal``);

val q656645_polynomial_def = new_definition (
  "q656645_polynomial_def",
  ``q656645_polynomial (zero : 'r) (p : num -> 'r) <=>
      FINITE {n : num | p n <> zero}``);

val q656645_poly_zero_def = new_definition (
  "q656645_poly_zero_def",
  ``q656645_poly_zero (zero : 'r) = (\n : num. zero)``);

val q656645_poly_add_def = new_definition (
  "q656645_poly_add_def",
  ``q656645_poly_add
      (add : 'r -> 'r -> 'r) (p : num -> 'r) q =
      (\n. add (p n) (q n))``);

val q656645_poly_neg_def = new_definition (
  "q656645_poly_neg_def",
  ``q656645_poly_neg (neg : 'r -> 'r) (p : num -> 'r) =
      (\n. neg (p n))``);

val q656645_poly_mul_def = new_definition (
  "q656645_poly_mul_def",
  ``q656645_poly_mul
      (zero : 'r) (add : 'r -> 'r -> 'r)
      (mul : 'r -> 'r -> 'r)
      (p : num -> 'r) (q : num -> 'r) (n : num) =
      ITSET
        (\ij acc.
          add (mul (p (FST ij)) (q (SND ij))) acc)
        {ij : num # num | FST ij + SND ij = n}
        zero``);

val Polynomial_isNoetherianRing =
  ``!(zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r).
      q656645_comm_ring zero oneR add mul neg /\
      q656645_noetherian (\x : 'r. T) zero add mul neg
      ==>
      q656645_noetherian
        (q656645_polynomial zero)
        (q656645_poly_zero zero)
        (q656645_poly_add add)
        (q656645_poly_mul zero add mul)
        (q656645_poly_neg neg)``;
