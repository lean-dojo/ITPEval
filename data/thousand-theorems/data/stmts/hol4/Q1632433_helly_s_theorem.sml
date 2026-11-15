(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1632433 (thousand-theorems__hol4__Q1632433), "Helly's theorem": for a
  finite family of convex sets in a finite-dimensional vector space over a
  linear ordered field, if the family has at least dimension plus one members
  and every subfamily of that size has nonempty intersection, then the whole
  family has nonempty intersection. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val helly_theorem =
  ``!(zero : 'r) (one : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (inv : 'r -> 'r)
      (leq : 'r -> 'r -> bool)
      (vzero : 'e) (vadd : 'e -> 'e -> 'e) (vneg : 'e -> 'e)
      (smul : 'r -> 'e -> 'e)
      (F : 'i -> 'e set) (s : 'i set).
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
        inv zero = zero /\
        (!x. x <> zero ==> mul x (inv x) = one) /\
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
      let lincomb =
        \(basis : 'e list) (coeff : num -> 'r).
          FOLDL
            (\acc i. vadd acc (smul (coeff i) (EL i basis)))
            vzero
            (GENLIST (\i. i) (LENGTH basis))
      in
      let is_basis =
        \(basis : 'e list).
          ALL_DISTINCT basis /\
          (!coeff : num -> 'r.
            lincomb basis coeff = vzero ==>
            !i. i < LENGTH basis ==> coeff i = zero) /\
          (!x : 'e.
            ?coeff : num -> 'r. lincomb basis coeff = x)
      in
      let finite_dimensional = (?basis : 'e list. is_basis basis)
      in
      let dimension = LENGTH (@basis : 'e list. is_basis basis)
      in
      let convex =
        \(c : 'e set).
          !x y a b.
            x IN c /\ y IN c /\
            leq zero a /\ leq zero b /\ add a b = one
            ==>
            vadd (smul a x) (smul b y) IN c
      in
      ordered_field /\
      module_axioms /\
      finite_dimensional /\
      FINITE s /\
      SUC dimension <= CARD s /\
      (!i. i IN s ==> convex (F i)) /\
      (!I : 'i set.
        I SUBSET s /\
        CARD I = SUC dimension
        ==>
        ?x : 'e. !i. i IN I ==> x IN F i)
      ==>
      ?x : 'e. !i. i IN s ==> x IN F i``;
