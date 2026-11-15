(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q26708, "Binomial theorem": over an arbitrary commutative semiring, the
  nth power of x + y equals the finite sum of the corresponding binomial
  terms. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory listTheory;

val q26708_comm_semiring_def = new_definition (
  "q26708_comm_semiring_def",
  ``q26708_comm_semiring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) <=>
      (!a b. addR a b = addR b a) /\
      (!a b c. addR (addR a b) c = addR a (addR b c)) /\
      (!a. addR zeroR a = a) /\
      (!a b. mulR a b = mulR b a) /\
      (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
      (!a. mulR oneR a = a) /\
      (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
      (!a. mulR zeroR a = zeroR)``);

val q26708_pow_def = new_definition (
  "q26708_pow_def",
  ``q26708_pow
      (oneR : 'r) (mulR : 'r -> 'r -> 'r) (x : 'r) (n : num) =
      FUNPOW (mulR x) n oneR``);

val q26708_nat_cast_def = new_definition (
  "q26708_nat_cast_def",
  ``q26708_nat_cast
      (zeroR : 'r) (oneR : 'r) (addR : 'r -> 'r -> 'r) (n : num) =
      FUNPOW (addR oneR) n zeroR``);

val q26708_sum_def = new_definition (
  "q26708_sum_def",
  ``q26708_sum
      (zeroR : 'r) (addR : 'r -> 'r -> 'r)
      (f : num -> 'r) (n : num) =
      FOLDR addR zeroR (GENLIST f (SUC n))``);

val q26708_choose_def = new_definition (
  "q26708_choose_def",
  ``q26708_choose (n : num) (m : num) =
      FACT n DIV (FACT m * FACT (n - m))``);

val add_pow =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (x : 'r) (y : 'r) (n : num).
      q26708_comm_semiring zeroR oneR addR mulR
      ==>
      q26708_pow oneR mulR (addR x y) n =
      q26708_sum zeroR addR
        (\m.
          mulR
            (mulR
              (q26708_pow oneR mulR x m)
              (q26708_pow oneR mulR y (n - m)))
            (q26708_nat_cast zeroR oneR addR (q26708_choose n m)))
        n``;
