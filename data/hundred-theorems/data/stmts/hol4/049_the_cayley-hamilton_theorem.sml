(*
  Statement-only formalization of "The Cayley-Hamilton Theorem" from Hundred
  Theorems artifact 049. For a square matrix over an arbitrary commutative
  ring on a finite index carrier, the characteristic polynomial det(XI - A)
  evaluates at the matrix to the zero matrix. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory ringTheory;

val cayley_hamilton_theorem =
  ``let poly_zero =
      \(r : 'a ring) (k : num). r.sum.id
    in
    let poly_one =
      \(r : 'a ring) (k : num).
        if k = 0 then r.prod.id else r.sum.id
    in
    let poly_add =
      \(r : 'a ring) (p : num -> 'a) (q : num -> 'a) (k : num).
        r.sum.op (p k) (q k)
    in
    let poly_neg =
      \(r : 'a ring) (p : num -> 'a) (k : num).
        r.sum.inv (p k)
    in
    let poly_mul =
      \(r : 'a ring) (p : num -> 'a) (q : num -> 'a) (k : num).
        ITSET
          (\i acc. r.sum.op (r.prod.op (p i) (q (k - i))) acc)
          (count (SUC k)) r.sum.id
    in
    let char_entry =
      \(r : 'a ring) (A : 'i -> 'i -> 'a)
       (i : 'i) (j : 'i) (k : num).
        r.sum.op
          (if i = j /\ k = 1 then r.prod.id else r.sum.id)
          (if k = 0 then r.sum.inv (A i j) else r.sum.id)
    in
    let det_term =
      \(r : 'a ring) (s : 'i -> bool) (A : 'i -> 'i -> 'a)
       (p : 'i -> 'i).
        let diagonal_product =
          ITSET
            (\i q. poly_mul r (char_entry r A i (p i)) q)
            s (poly_one r)
        in
          if evenperm p then diagonal_product
          else poly_neg r diagonal_product
    in
    let char_poly =
      \(r : 'a ring) (s : 'i -> bool) (A : 'i -> 'i -> 'a).
        ITSET
          (\p q. poly_add r (det_term r s A p) q)
          {p : 'i -> 'i | p permutes s} (poly_zero r)
    in
    let matrix_zero =
      \(r : 'a ring) (s : 'i -> bool) (i : 'i) (j : 'i).
        r.sum.id
    in
    let matrix_one =
      \(r : 'a ring) (s : 'i -> bool) (i : 'i) (j : 'i).
        if i IN s /\ j IN s /\ i = j then r.prod.id else r.sum.id
    in
    let matrix_add =
      \(r : 'a ring) (s : 'i -> bool)
       (A : 'i -> 'i -> 'a) (B : 'i -> 'i -> 'a)
       (i : 'i) (j : 'i).
        if i IN s /\ j IN s
        then r.sum.op (A i j) (B i j)
        else r.sum.id
    in
    let matrix_mul =
      \(r : 'a ring) (s : 'i -> bool)
       (A : 'i -> 'i -> 'a) (B : 'i -> 'i -> 'a)
       (i : 'i) (j : 'i).
        if i IN s /\ j IN s
        then
          ITSET
            (\k acc. r.sum.op (r.prod.op (A i k) (B k j)) acc)
            s r.sum.id
        else r.sum.id
    in
    let matrix_scale =
      \(r : 'a ring) (s : 'i -> bool) (c : 'a)
       (A : 'i -> 'i -> 'a) (i : 'i) (j : 'i).
        if i IN s /\ j IN s
        then r.prod.op c (A i j)
        else r.sum.id
    in
    let matrix_pow =
      \(r : 'a ring) (s : 'i -> bool)
       (A : 'i -> 'i -> 'a) (k : num).
        FUNPOW (\B. matrix_mul r s B A) k (matrix_one r s)
    in
    let matrix_poly_eval =
      \(r : 'a ring) (s : 'i -> bool) (p : num -> 'a)
       (A : 'i -> 'i -> 'a).
        ITSET
          (\k B.
            matrix_add r s
              (matrix_scale r s (p k) (matrix_pow r s A k)) B)
          (count (SUC (CARD s))) (matrix_zero r s)
    in
      !(r : 'a ring) (s : 'i -> bool) (A : 'i -> 'i -> 'a).
        Ring r /\
        FINITE s /\
        (!i j. i IN s /\ j IN s ==> A i j IN r.carrier)
        ==>
        matrix_poly_eval r s (char_poly r s A) A = matrix_zero r s``;
