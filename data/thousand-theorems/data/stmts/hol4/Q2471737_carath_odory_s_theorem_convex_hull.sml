(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2471737 (thousand-theorems__hol4__Q2471737), "Carathéodory's theorem
  (convex hull)": the convex hull of a set in a module over a linear ordered
  field is the union of the convex hulls of its finite affine-independent
  subsets. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val convexHull_eq_union =
  ``!(zero : 'r) (one : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (recip : 'r -> 'r)
      (leq : 'r -> 'r -> bool)
      (vzero : 'e) (vadd : 'e -> 'e -> 'e) (vneg : 'e -> 'e)
      (smul : 'r -> 'e -> 'e) (s : 'e set).
      let q2471737_field_axioms = (
        ~(one = zero) /\
        (!x y. add x y = add y x) /\
        (!x y z. add (add x y) z = add x (add y z)) /\
        (!x. add x zero = x) /\
        (!x. add x (neg x) = zero) /\
        (!x y. mul x y = mul y x) /\
        (!x y z. mul (mul x y) z = mul x (mul y z)) /\
        (!x. mul x one = x) /\
        (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
        (!x. ~(x = zero) ==> mul x (recip x) = one) /\
        (!x. leq x x) /\
        (!x y z. leq x y /\ leq y z ==> leq x z) /\
        (!x y. leq x y /\ leq y x ==> x = y) /\
        (!x y. leq x y \/ leq y x) /\
        (!x y z. leq x y ==> leq (add z x) (add z y)) /\
        (!x y. leq zero x /\ leq zero y ==> leq zero (mul x y)))
      in
      let q2471737_module_axioms = (
        (!x y. vadd x y = vadd y x) /\
        (!x y z. vadd (vadd x y) z = vadd x (vadd y z)) /\
        (!x. vadd x vzero = x) /\
        (!x. vadd x (vneg x) = vzero) /\
        (!x. smul one x = x) /\
        (!a b x. smul (mul a b) x = smul a (smul b x)) /\
        (!a b x. smul (add a b) x = vadd (smul a x) (smul b x)) /\
        (!a x y. smul a (vadd x y) = vadd (smul a x) (smul a y)))
      in
      let q2471737_scalar_sum = (
        \(w : 'e -> 'r) (t : 'e set).
          ITSET (\x acc. add (w x) acc) t zero)
      in
      let q2471737_vector_sum = (
        \(w : 'e -> 'r) (t : 'e set).
          ITSET (\x acc. vadd (smul (w x) x) acc) t vzero)
      in
      let q2471737_affine_independent = (
        \(t : 'e set).
          FINITE t /\
          !w : 'e -> 'r.
            q2471737_scalar_sum w t = zero /\
            q2471737_vector_sum w t = vzero
            ==>
            !x. x IN t ==> w x = zero)
      in
      let q2471737_convex_hull = (
        \(s : 'e set).
          {p : 'e |
            ?t : 'e set. ?w : 'e -> 'r.
              FINITE t /\
              t SUBSET s /\
              (!x. x IN t ==> leq zero (w x)) /\
              q2471737_scalar_sum w t = one /\
              q2471737_vector_sum w t = p})
      in
        q2471737_field_axioms /\
        q2471737_module_axioms
        ==>
        q2471737_convex_hull s =
        {p : 'e |
          ?t : 'e set.
            t SUBSET s /\
            q2471737_affine_independent t /\
            p IN q2471737_convex_hull t}``;
