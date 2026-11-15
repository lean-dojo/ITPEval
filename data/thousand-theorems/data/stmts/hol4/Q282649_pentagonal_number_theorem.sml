(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q282649, "Pentagonal number theorem": over an arbitrary commutative ring
  with an arbitrary topology, the infinite product of the formal power series
  1 - X^(n+1) converges coefficientwise to the generalized pentagonal series.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory topologyTheory;

val q282649_comm_ring_def = new_definition (
  "q282649_comm_ring_def",
  ``q282649_comm_ring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r) <=>
      (!(x : 'r) (y : 'r) (z : 'r).
         addR (addR x y) z = addR x (addR y z)) /\
      (!(x : 'r) (y : 'r). addR x y = addR y x) /\
      (!(x : 'r). addR zeroR x = x) /\
      (!(x : 'r). addR (negR x) x = zeroR) /\
      (!(x : 'r) (y : 'r) (z : 'r).
         mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!(x : 'r) (y : 'r). mulR x y = mulR y x) /\
      (!(x : 'r). mulR oneR x = x) /\
      (!(x : 'r) (y : 'r) (z : 'r).
         mulR x (addR y z) = addR (mulR x y) (mulR x z))``);

val q282649_series_one_def = new_definition (
  "q282649_series_one_def",
  ``q282649_series_one (zeroR : 'r) (oneR : 'r) =
      (\n : num. if n = 0 then oneR else zeroR)``);

val q282649_series_mul_def = new_definition (
  "q282649_series_mul_def",
  ``q282649_series_mul
      (zeroR : 'r) (addR : 'r -> 'r -> 'r)
      (mulR : 'r -> 'r -> 'r)
      (f : num -> 'r) (g : num -> 'r) =
      (\n : num.
        FOLDR addR zeroR
          (GENLIST (\i. mulR (f i) (g (n - i))) (SUC n)))``);

val q282649_one_sub_X_pow_def = new_definition (
  "q282649_one_sub_X_pow_def",
  ``q282649_one_sub_X_pow
      (zeroR : 'r) (oneR : 'r) (negR : 'r -> 'r) (n : num) =
      (\k : num.
        if k = 0 then oneR
        else if k = SUC n then negR oneR
        else zeroR)``);

val q282649_series_finprod_def = new_definition (
  "q282649_series_finprod_def",
  ``q282649_series_finprod
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (f : num -> num -> 'r) (s : num set) =
      ITSET
        (\i acc. q282649_series_mul zeroR addR mulR (f i) acc)
        s
        (q282649_series_one zeroR oneR)``);

val q282649_pentagonal_def = new_definition (
  "q282649_pentagonal_def",
  ``q282649_pentagonal (k : int) =
      if 0 <= k then
        let n = Num k in n * (3 * n - 1) DIV 2
      else
        let n = Num (ABS k) in n * (3 * n + 1) DIV 2``);

val q282649_neg_one_pow_def = new_definition (
  "q282649_neg_one_pow_def",
  ``q282649_neg_one_pow (oneR : 'r) (negR : 'r -> 'r) (k : int) =
      if EVEN (Num (ABS k)) then oneR else negR oneR``);

val q282649_pentagonal_series_def = new_definition (
  "q282649_pentagonal_series_def",
  ``q282649_pentagonal_series
      (zeroR : 'r) (oneR : 'r) (negR : 'r -> 'r) =
      (\n : num.
        if ?k : int. q282649_pentagonal k = n then
          q282649_neg_one_pow oneR negR
            (@k : int. q282649_pentagonal k = n)
        else
          zeroR)``);

val q282649_has_prod_pi_def = new_definition (
  "q282649_has_prod_pi_def",
  ``q282649_has_prod_pi
      (top : 'r topology)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (f : num -> num -> 'r) (a : num -> 'r) <=>
      !k : num. !u : 'r set.
        open_in top u /\ a k IN u ==>
        ?s0 : num set.
          FINITE s0 /\
          !s : num set.
            FINITE s /\ s0 SUBSET s ==>
            q282649_series_finprod zeroR oneR addR mulR f s k IN u``);

val hasProd_one_sub_X_pow =
  ``!(top : 'r topology)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r).
      q282649_comm_ring zeroR oneR addR mulR negR /\
      topspace top = UNIV
      ==>
      q282649_has_prod_pi top zeroR oneR addR mulR
        (q282649_one_sub_X_pow zeroR oneR negR)
        (q282649_pentagonal_series zeroR oneR negR)``;
