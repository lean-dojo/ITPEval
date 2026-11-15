(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1551745, "Binomial inverse theorem": over an arbitrary ring and arbitrary
  finite row and column index types, three matrix invertibility assumptions
  imply the binomial inverse formula for A + U*C*V. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q1551745_ring_def = new_definition (
  "q1551745_ring_def",
  ``q1551745_ring
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (negR : 'a -> 'a)
      (mulR : 'a -> 'a -> 'a) <=>
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x y. addR x y = addR y x) /\
      (!x. addR zeroR x = x /\ addR x zeroR = x) /\
      (!x. addR (negR x) x = zeroR /\ addR x (negR x) = zeroR) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR oneR x = x /\ mulR x oneR = x) /\
      (!x y z. mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
      (!x y z. mulR (addR x y) z = addR (mulR x z) (mulR y z))``);

val q1551745_matrix_eq_def = new_definition (
  "q1551745_matrix_eq_def",
  ``q1551745_matrix_eq
      (rows : 'i set) (cols : 'j set)
      (M : 'i -> 'j -> 'a) (N : 'i -> 'j -> 'a) <=>
      !i j. i IN rows /\ j IN cols ==> M i j = N i j``);

val q1551745_matrix_one_def = new_definition (
  "q1551745_matrix_one_def",
  ``q1551745_matrix_one
      (zeroR : 'a) (oneR : 'a) (s : 'i set) (i : 'i) (j : 'i) =
      if i IN s /\ j IN s /\ i = j then oneR else zeroR``);

val q1551745_matrix_add_def = new_definition (
  "q1551745_matrix_add_def",
  ``q1551745_matrix_add
      (zeroR : 'a) (addR : 'a -> 'a -> 'a)
      (rows : 'i set) (cols : 'j set)
      (M : 'i -> 'j -> 'a) (N : 'i -> 'j -> 'a)
      (i : 'i) (j : 'j) =
      if i IN rows /\ j IN cols then addR (M i j) (N i j) else zeroR``);

val q1551745_matrix_sub_def = new_definition (
  "q1551745_matrix_sub_def",
  ``q1551745_matrix_sub
      (zeroR : 'a) (addR : 'a -> 'a -> 'a) (negR : 'a -> 'a)
      (rows : 'i set) (cols : 'j set)
      (M : 'i -> 'j -> 'a) (N : 'i -> 'j -> 'a)
      (i : 'i) (j : 'j) =
      if i IN rows /\ j IN cols
      then addR (M i j) (negR (N i j))
      else zeroR``);

val q1551745_matrix_mul_def = new_definition (
  "q1551745_matrix_mul_def",
  ``q1551745_matrix_mul
      (zeroR : 'a) (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a)
      (rows : 'i set) (inner : 'j set) (cols : 'k set)
      (M : 'i -> 'j -> 'a) (N : 'j -> 'k -> 'a)
      (i : 'i) (k : 'k) =
      if i IN rows /\ k IN cols
      then
        ITSET
          (\j acc. addR (mulR (M i j) (N j k)) acc)
          inner zeroR
      else zeroR``);

val q1551745_matrix_inverse_def = new_definition (
  "q1551745_matrix_inverse_def",
  ``q1551745_matrix_inverse
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (mulR : 'a -> 'a -> 'a)
      (s : 'i set) (M : 'i -> 'i -> 'a) (Minv : 'i -> 'i -> 'a) <=>
      q1551745_matrix_eq s s
        (q1551745_matrix_mul zeroR addR mulR s s s M Minv)
        (q1551745_matrix_one zeroR oneR s) /\
      q1551745_matrix_eq s s
        (q1551745_matrix_mul zeroR addR mulR s s s Minv M)
        (q1551745_matrix_one zeroR oneR s)``);

val binomial_inverse_theorem =
  ``!(zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (negR : 'a -> 'a)
      (mulR : 'a -> 'a -> 'a)
      (s : 'n set) (t : 'm set)
      (A : 'n -> 'n -> 'a) (U : 'n -> 'm -> 'a)
      (C : 'm -> 'm -> 'a) (V : 'm -> 'n -> 'a)
      (Ainv : 'n -> 'n -> 'a) (Dinv : 'm -> 'm -> 'a)
      (Binv : 'n -> 'n -> 'a).
      let B =
        q1551745_matrix_add zeroR addR s s A
          (q1551745_matrix_mul zeroR addR mulR s t s
            (q1551745_matrix_mul zeroR addR mulR s t t U C) V)
      in
      let D =
        q1551745_matrix_add zeroR addR t t C
          (q1551745_matrix_mul zeroR addR mulR t t t
            (q1551745_matrix_mul zeroR addR mulR t s t
              (q1551745_matrix_mul zeroR addR mulR t s s
                (q1551745_matrix_mul zeroR addR mulR t t s C V) Ainv)
              U)
            C)
      in
      let correction =
        q1551745_matrix_mul zeroR addR mulR s s s
          (q1551745_matrix_mul zeroR addR mulR s t s
            (q1551745_matrix_mul zeroR addR mulR s t t
              (q1551745_matrix_mul zeroR addR mulR s t t
                (q1551745_matrix_mul zeroR addR mulR s t t
                  (q1551745_matrix_mul zeroR addR mulR s s t Ainv U) C)
                Dinv)
              C)
            V)
          Ainv
      in
        q1551745_ring zeroR oneR addR negR mulR /\
        FINITE s /\
        FINITE t /\
        q1551745_matrix_inverse zeroR oneR addR mulR s A Ainv /\
        q1551745_matrix_inverse zeroR oneR addR mulR t D Dinv /\
        q1551745_matrix_inverse zeroR oneR addR mulR s B Binv
        ==>
        q1551745_matrix_eq s s Binv
          (q1551745_matrix_sub zeroR addR negR s s Ainv correction)``;
