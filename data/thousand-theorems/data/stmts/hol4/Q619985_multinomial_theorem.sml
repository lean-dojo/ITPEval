(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q619985, "Multinomial theorem": in an arbitrary semiring, the power of a
  finite sum of pairwise commuting elements expands over exponent functions
  of total degree n with multinomial coefficients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory pred_setTheory;

val q619985_semiring_def = new_definition (
  "q619985_semiring_def",
  ``q619985_semiring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) <=>
      (!a b c. addR (addR a b) c = addR a (addR b c)) /\
      (!a b. addR a b = addR b a) /\
      (!a. addR zeroR a = a) /\
      (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
      (!a. mulR oneR a = a) /\
      (!a. mulR a oneR = a) /\
      (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
      (!a b c. mulR (addR a b) c = addR (mulR a c) (mulR b c)) /\
      (!a. mulR zeroR a = zeroR) /\
      (!a. mulR a zeroR = zeroR)``);

val q619985_pow_def = new_definition (
  "q619985_pow_def",
  ``q619985_pow
      (oneR : 'r) (mulR : 'r -> 'r -> 'r) (x : 'r) (n : num) =
      FUNPOW (mulR x) n oneR``);

val q619985_nat_cast_def = new_definition (
  "q619985_nat_cast_def",
  ``q619985_nat_cast
      (zeroR : 'r) (oneR : 'r) (addR : 'r -> 'r -> 'r) (n : num) =
      FUNPOW (addR oneR) n zeroR``);

val q619985_sum_def = new_definition (
  "q619985_sum_def",
  ``q619985_sum
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (s : 'i -> bool) (f : 'i -> 'a) =
      ITSET (\i acc. add (f i) acc) s zero``);

val q619985_product_def = new_definition (
  "q619985_product_def",
  ``q619985_product
      (oneR : 'a) (mulR : 'a -> 'a -> 'a)
      (s : 'i -> bool) (f : 'i -> 'a) =
      ITSET (\i acc. mulR (f i) acc) s oneR``);

val q619985_num_sum_def = new_definition (
  "q619985_num_sum_def",
  ``q619985_num_sum (s : 'i -> bool) (k : 'i -> num) =
      ITSET (\i acc. k i + acc) s 0``);

val q619985_pi_antidiag_def = new_definition (
  "q619985_pi_antidiag_def",
  ``q619985_pi_antidiag (s : 'i -> bool) (n : num) =
      {k : 'i -> num |
        q619985_num_sum s k = n /\
        !i. k i <> 0 ==> i IN s}``);

val q619985_multinomial_def = new_definition (
  "q619985_multinomial_def",
  ``q619985_multinomial (s : 'i -> bool) (k : 'i -> num) =
      FACT (q619985_num_sum s k) DIV
        ITSET (\i acc. FACT (k i) * acc) s 1``);

val Finset_sum_pow_eq_sum_piAntidiag_of_commute =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (s : 'i -> bool) (f : 'i -> 'r) (n : num).
      q619985_semiring zeroR oneR addR mulR /\
      FINITE s /\
      (!i j.
        i IN s /\ j IN s /\ i <> j ==>
        mulR (f i) (f j) = mulR (f j) (f i))
      ==>
      q619985_pow oneR mulR (q619985_sum zeroR addR s f) n =
      q619985_sum zeroR addR (q619985_pi_antidiag s n)
        (\k.
          mulR
            (q619985_nat_cast zeroR oneR addR
              (q619985_multinomial s k))
            (q619985_product oneR mulR s
              (\i. q619985_pow oneR mulR (f i) (k i))))``;
