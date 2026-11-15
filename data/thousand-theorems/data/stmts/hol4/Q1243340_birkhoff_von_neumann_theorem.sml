(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1243340, "Birkhoff–Von Neumann theorem": over any linear ordered field and
  finite index type, the doubly stochastic matrices are exactly the convex
  hull of the permutation matrices. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory permutesTheory;

val doublyStochastic_eq_convexHull_permMatrix =
  ``!(zero : 'r) (one : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (recip : 'r -> 'r)
      (leq : 'r -> 'r -> bool) (s : 'i set).
      let ordered_field = (
        one <> zero /\
        (!x y. add x y = add y x) /\
        (!x y z. add (add x y) z = add x (add y z)) /\
        (!x. add x zero = x) /\
        (!x. add x (neg x) = zero) /\
        (!x y. mul x y = mul y x) /\
        (!x y z. mul (mul x y) z = mul x (mul y z)) /\
        (!x. mul x one = x) /\
        (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
        recip zero = zero /\
        (!x. x <> zero ==> mul x (recip x) = one) /\
        (!x. leq x x) /\
        (!x y z. leq x y /\ leq y z ==> leq x z) /\
        (!x y. leq x y /\ leq y x ==> x = y) /\
        (!x y. leq x y \/ leq y x) /\
        (!x y z. leq x y ==> leq (add z x) (add z y)) /\
        (!x y. leq zero x /\ leq zero y ==> leq zero (mul x y)))
      in
      let index_sum =
        \(f : 'i -> 'r) (t : 'i set).
          ITSET (\i acc. add (f i) acc) t zero
      in
      let permutation_sum =
        \(f : ('i -> 'i) -> 'r) (t : ('i -> 'i) set).
          ITSET (\p acc. add (f p) acc) t zero
      in
      let permutations = {p : 'i -> 'i | p permutes s}
      in
      let permutation_matrix =
        \(p : 'i -> 'i) (i : 'i) (j : 'i).
          if i IN s /\ j IN s /\ p i = j then one else zero
      in
      let matrix_on_carrier =
        \(M : 'i -> 'i -> 'r).
          !i j. ~(i IN s /\ j IN s) ==> M i j = zero
      in
      let doubly_stochastic =
        \(M : 'i -> 'i -> 'r).
          matrix_on_carrier M /\
          (!i j. i IN s /\ j IN s ==> leq zero (M i j)) /\
          (!i. i IN s ==> index_sum (M i) s = one) /\
          (!j. j IN s ==> index_sum (\i. M i j) s = one)
      in
      let convex_hull_of_permutation_matrices =
        \(M : 'i -> 'i -> 'r).
          matrix_on_carrier M /\
          ?t : ('i -> 'i) set. ?w : ('i -> 'i) -> 'r.
            FINITE t /\
            t SUBSET permutations /\
            (!p. p IN t ==> leq zero (w p)) /\
            permutation_sum w t = one /\
            (!i j.
              permutation_sum
                (\p. mul (w p) (permutation_matrix p i j))
                t =
              M i j)
      in
        ordered_field /\ FINITE s
        ==>
        {M : 'i -> 'i -> 'r | doubly_stochastic M} =
        {M : 'i -> 'i -> 'r |
          convex_hull_of_permutation_matrices M}``;
