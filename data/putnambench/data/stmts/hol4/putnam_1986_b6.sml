(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b6:
  a transpose identity for square matrices over an arbitrary field, assuming
  two matrix products are symmetric and a mixed-product difference is the
  identity matrix. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1986_b6 =
  ``!(n : num) (zeroR oneR : 'a)
      (addR mulR : 'a -> 'a -> 'a)
      (negR invR : 'a -> 'a)
      (A B C D : 'i -> 'i -> 'a).
      let field_axioms =
        zeroR <> oneR /\
        (!x. addR zeroR x = x) /\
        (!x. addR (negR x) x = zeroR) /\
        (!x y. addR x y = addR y x) /\
        (!x y z. addR (addR x y) z = addR x (addR y z)) /\
        (!x. mulR oneR x = x) /\
        (!x y. mulR x y = mulR y x) /\
        (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
        (!x y z.
           mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
        (!x. x <> zeroR ==> mulR (invR x) x = oneR)
      in
      let matrix_transpose =
        \M : 'i -> 'i -> 'a. \i j. M j i
      in
      let matrix_mul =
        \M N : 'i -> 'i -> 'a. \i j.
          ITSET
            (\k acc. addR (mulR (M i k) (N k j)) acc)
            (UNIV : 'i set) zeroR
      in
      let matrix_sub =
        \M N : 'i -> 'i -> 'a. \i j.
          addR (M i j) (negR (N i j))
      in
      let matrix_one =
        \i : 'i. \j : 'i. if i = j then oneR else zeroR
      in
        field_axioms /\
        FINITE (UNIV : 'i set) /\
        0 < n /\
        CARD (UNIV : 'i set) = n /\
        matrix_mul A (matrix_transpose B) =
          matrix_transpose (matrix_mul A (matrix_transpose B)) /\
        matrix_mul C (matrix_transpose D) =
          matrix_transpose (matrix_mul C (matrix_transpose D)) /\
        matrix_sub
          (matrix_mul A (matrix_transpose D))
          (matrix_mul B (matrix_transpose C)) =
          matrix_one
        ==>
        matrix_sub
          (matrix_mul (matrix_transpose A) D)
          (matrix_mul (matrix_transpose C) B) =
          matrix_one``;
