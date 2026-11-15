(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1471282 (thousand-theorems__hol4__Q1471282), "Radon's theorem": every
  affinely dependent family in a vector space over a linear ordered field
  admits a partition whose two convex hulls intersect. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val radon_partition =
  ``!(zero : 'r) (one : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (recip : 'r -> 'r)
      (leq : 'r -> 'r -> bool)
      (vzero : 'e) (vadd : 'e -> 'e -> 'e) (vneg : 'e -> 'e)
      (smul : 'r -> 'e -> 'e) (f : 'i -> 'e).
      let ordered_field_axioms = (
        ~(one = zero) /\
        (!x y. add x y = add y x) /\
        (!x y z. add (add x y) z = add x (add y z)) /\
        (!x. add x zero = x) /\
        (!x. add x (neg x) = zero) /\
        (!x y. mul x y = mul y x) /\
        (!x y z. mul (mul x y) z = mul x (mul y z)) /\
        (!x. mul x one = x) /\
        (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
        (!x. x <> zero ==> mul x (recip x) = one) /\
        (!x. leq x x) /\
        (!x y z. leq x y /\ leq y z ==> leq x z) /\
        (!x y. leq x y /\ leq y x ==> x = y) /\
        (!x y. leq x y \/ leq y x) /\
        (!x y z. leq x y ==> leq (add z x) (add z y)) /\
        (!x y. leq zero x /\ leq zero y ==> leq zero (mul x y)))
      in
      let module_axioms = (
        (!x y. vadd x y = vadd y x) /\
        (!x y z. vadd (vadd x y) z = vadd x (vadd y z)) /\
        (!x. vadd x vzero = x) /\
        (!x. vadd x (vneg x) = vzero) /\
        (!x. smul one x = x) /\
        (!a b x. smul (mul a b) x = smul a (smul b x)) /\
        (!a b x. smul (add a b) x = vadd (smul a x) (smul b x)) /\
        (!a x y. smul a (vadd x y) = vadd (smul a x) (smul a y)))
      in
      let scalar_sum = (
        \(w : 'i -> 'r) (s : 'i set).
          ITSET (\i acc. add (w i) acc) s zero)
      in
      let vector_sum = (
        \(g : 'i -> 'e) (w : 'i -> 'r) (s : 'i set).
          ITSET (\i acc. vadd (smul (w i) (g i)) acc) s vzero)
      in
      let affine_independent = (
        \(g : 'i -> 'e).
          !s : 'i set. !w : 'i -> 'r.
            FINITE s /\
            scalar_sum w s = zero /\
            vector_sum g w s = vzero
            ==>
            !i. i IN s ==> w i = zero)
      in
      let in_convex_hull = (
        \(g : 'i -> 'e) (indices : 'i set) (p : 'e).
          ?s : 'i set. ?w : 'i -> 'r.
            FINITE s /\
            s SUBSET indices /\
            (!i. i IN s ==> leq zero (w i)) /\
            scalar_sum w s = one /\
            vector_sum g w s = p)
      in
        ordered_field_axioms /\
        module_axioms /\
        ~affine_independent f
        ==>
        ?I : 'i set. ?p : 'e.
          in_convex_hull f I p /\
          in_convex_hull f (COMPL I) p``;
