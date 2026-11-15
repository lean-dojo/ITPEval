(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q7660749, "Sylvester's determinant theorem": over an arbitrary commutative
  ring, det(I + AB) = det(I + BA) for rectangular matrices with finite row
  and column index carriers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory permutesTheory ringTheory;

val Matrix_det_one_add_mul_comm =
  ``let matrix_det_m =
      \(r : 'a ring) (s : 'm set) (M : 'm -> 'm -> 'a).
        ITSET
          (\p acc.
            r.sum.op
              (let diagonal_product =
                 ITSET
                   (\i product. r.prod.op (M i (p i)) product)
                   s r.prod.id
               in
                 if evenperm p then diagonal_product
                 else r.sum.inv diagonal_product)
              acc)
          {p : 'm -> 'm | p permutes s} r.sum.id
    in
    let matrix_det_n =
      \(r : 'a ring) (s : 'n set) (M : 'n -> 'n -> 'a).
        ITSET
          (\p acc.
            r.sum.op
              (let diagonal_product =
                 ITSET
                   (\i product. r.prod.op (M i (p i)) product)
                   s r.prod.id
               in
                 if evenperm p then diagonal_product
                 else r.sum.inv diagonal_product)
              acc)
          {p : 'n -> 'n | p permutes s} r.sum.id
    in
    let matrix_one_m =
      \(r : 'a ring) (s : 'm set) (i : 'm) (j : 'm).
        if i IN s /\ j IN s /\ i = j then r.prod.id else r.sum.id
    in
    let matrix_one_n =
      \(r : 'a ring) (s : 'n set) (i : 'n) (j : 'n).
        if i IN s /\ j IN s /\ i = j then r.prod.id else r.sum.id
    in
    let matrix_add_m =
      \(r : 'a ring) (s : 'm set)
       (M : 'm -> 'm -> 'a) (N : 'm -> 'm -> 'a)
       (i : 'm) (j : 'm).
        if i IN s /\ j IN s
        then r.sum.op (M i j) (N i j)
        else r.sum.id
    in
    let matrix_add_n =
      \(r : 'a ring) (s : 'n set)
       (M : 'n -> 'n -> 'a) (N : 'n -> 'n -> 'a)
       (i : 'n) (j : 'n).
        if i IN s /\ j IN s
        then r.sum.op (M i j) (N i j)
        else r.sum.id
    in
    let matrix_mul_ab =
      \(r : 'a ring) (rows : 'm set) (inner : 'n set)
       (cols : 'm set)
       (M : 'm -> 'n -> 'a) (N : 'n -> 'm -> 'a)
       (i : 'm) (k : 'm).
        if i IN rows /\ k IN cols
        then
          ITSET
            (\j acc. r.sum.op (r.prod.op (M i j) (N j k)) acc)
            inner r.sum.id
        else r.sum.id
    in
    let matrix_mul_ba =
      \(r : 'a ring) (rows : 'n set) (inner : 'm set)
       (cols : 'n set)
       (M : 'n -> 'm -> 'a) (N : 'm -> 'n -> 'a)
       (i : 'n) (k : 'n).
        if i IN rows /\ k IN cols
        then
          ITSET
            (\j acc. r.sum.op (r.prod.op (M i j) (N j k)) acc)
            inner r.sum.id
        else r.sum.id
    in
      !(r : 'a ring) (s : 'm set) (t : 'n set)
       (A : 'm -> 'n -> 'a) (B : 'n -> 'm -> 'a).
        Ring r /\
        FINITE s /\
        FINITE t /\
        (!i j. i IN s /\ j IN t ==> A i j IN r.carrier) /\
        (!j i. j IN t /\ i IN s ==> B j i IN r.carrier)
        ==>
        matrix_det_m r s
          (matrix_add_m r s (matrix_one_m r s)
            (matrix_mul_ab r s t s A B)) =
        matrix_det_n r t
          (matrix_add_n r t (matrix_one_n r t)
            (matrix_mul_ba r t s t B A))``;
