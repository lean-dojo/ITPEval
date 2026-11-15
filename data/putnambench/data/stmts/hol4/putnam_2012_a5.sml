(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a5:
  affine maps on n-dimensional vector spaces over a prime finite field have
  a full orbit of zero exactly in dimension one or in dimension two over the
  field of two elements. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory ringTheory;

val putnam_2012_a5 =
  ``!(r : 'a ring) (n p : num).
      let finite_field =
        \r : 'a ring.
          Ring r /\
          FINITE r.carrier /\
          (!x.
             x IN r.carrier /\ x <> r.sum.id
             ==>
             ?y.
               y IN r.carrier /\
               r.prod.op x y = r.prod.id /\
               r.prod.op y x = r.prod.id)
      in
      let zero_vector =
        \i : 'i. r.sum.id
      in
      let matrix_vector =
        \M : 'i -> 'i -> 'a.
        \x : 'i -> 'a.
        \i : 'i.
          ITSET
            (\j acc. r.sum.op (r.prod.op (M i j) (x j)) acc)
            (UNIV : 'i set)
            r.sum.id
      in
      let affine =
        \M : 'i -> 'i -> 'a.
        \v : 'i -> 'a.
        \x : 'i -> 'a.
        \i : 'i.
          r.sum.op (v i) (matrix_vector M x i)
      in
        finite_field r /\
        CARD r.carrier = p /\
        FINITE (UNIV : 'i set) /\
        CARD (UNIV : 'i set) = n /\
        0 < n /\
        prime p
        ==>
        ((n = 1 \/ (n = 2 /\ p = 2)) <=>
         ?M : 'i -> 'i -> 'a.
         ?v : 'i -> 'a.
           (!i j : 'i. M i j IN r.carrier) /\
           (!i : 'i. v i IN r.carrier) /\
           !k l : num.
             1 <= k /\
             k <= p ** n /\
             1 <= l /\
             l <= p ** n /\
             k <> l
             ==>
             FUNPOW (affine M v) k zero_vector <>
             FUNPOW (affine M v) l zero_vector)``;
