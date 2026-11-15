(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q570779, "Vieta's formulas": over a commutative semiring, the product of
  the linear polynomials X + C r indexed by a finite multiset equals the sum
  whose coefficients are its elementary symmetric functions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory bagTheory pred_setTheory;

val q570779_comm_semiring_def = new_definition (
  "q570779_comm_semiring_def",
  ``q570779_comm_semiring
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a) <=>
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x y. addR x y = addR y x) /\
      (!x. addR zeroR x = x) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x y. mulR x y = mulR y x) /\
      (!x. mulR oneR x = x) /\
      (!x y z. mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
      (!x. mulR zeroR x = zeroR)``);

val q570779_poly_one_def = new_definition (
  "q570779_poly_one_def",
  ``q570779_poly_one (zeroR : 'a) (oneR : 'a) (n : num) =
      if n = 0 then oneR else zeroR``);

val q570779_linear_def = new_definition (
  "q570779_linear_def",
  ``q570779_linear (zeroR : 'a) (oneR : 'a) (r : 'a) (n : num) =
      if n = 0 then r else if n = 1 then oneR else zeroR``);

val q570779_poly_mul_def = new_definition (
  "q570779_poly_mul_def",
  ``q570779_poly_mul
      (zeroR : 'a) (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a)
      (p : num -> 'a) (q : num -> 'a) (n : num) =
      ITSET
        (\i acc. addR (mulR (p i) (q (n - i))) acc)
        (count (SUC n))
        zeroR``);

val q570779_prod_linear_def = new_definition (
  "q570779_prod_linear_def",
  ``q570779_prod_linear
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a)
      (s : 'a bag) =
      ITBAG
        (\r p.
           q570779_poly_mul zeroR addR mulR
             (q570779_linear zeroR oneR r) p)
        s
        (q570779_poly_one zeroR oneR)``);

val q570779_esymm_def = new_definition (
  "q570779_esymm_def",
  ``q570779_esymm
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a)
      (s : 'a bag) =
      ITBAG
        (\r e k.
           if k = 0
           then oneR
           else addR (e k) (mulR r (e (PRE k))))
        s
        (\k. if k = 0 then oneR else zeroR)``);

val q570779_monomial_def = new_definition (
  "q570779_monomial_def",
  ``q570779_monomial
      (zeroR : 'a) (c : 'a) (degree : num) (n : num) =
      if n = degree then c else zeroR``);

val q570779_sum_esymm_def = new_definition (
  "q570779_sum_esymm_def",
  ``q570779_sum_esymm
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a)
      (s : 'a bag) (n : num) =
      ITSET
        (\j acc.
           addR
             (q570779_monomial zeroR
               (q570779_esymm zeroR oneR addR mulR s j)
               (BAG_CARD s - j)
               n)
             acc)
        (count (SUC (BAG_CARD s)))
        zeroR``);

val Multiset_prod_X_add_C_eq_sum_esymm =
  ``!(zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a)
      (s : 'a bag).
      q570779_comm_semiring zeroR oneR addR mulR /\
      FINITE_BAG s
      ==>
      q570779_prod_linear zeroR oneR addR mulR s =
      q570779_sum_esymm zeroR oneR addR mulR s``;
