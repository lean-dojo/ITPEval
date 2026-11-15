(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4830725, "Ax–Grothendieck theorem": over an algebraically closed field
  with finitely many variables, an injective polynomial self-map of an
  ideal's zero locus is surjective on that zero locus. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pairTheory pred_setTheory;

val ax_grothendieck_zeroLocus =
  ``!(kzero : 'k) (kone : 'k)
      (kadd : 'k -> 'k -> 'k)
      (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k)
      (kinv : 'k -> 'k)
      (I : ((('i -> num) -> 'k) -> bool))
      (p : 'i -> ('i -> num) -> 'k).
      let field_axioms =
        (kzero <> kone /\
        (!x. kadd kzero x = x) /\
        (!x. kadd (kneg x) x = kzero) /\
        (!x y. kadd x y = kadd y x) /\
        (!x y z. kadd (kadd x y) z = kadd x (kadd y z)) /\
        (!x. kmul kone x = x) /\
        (!x y. kmul x y = kmul y x) /\
        (!x y z. kmul (kmul x y) z = kmul x (kmul y z)) /\
        (!x y z.
           kmul x (kadd y z) = kadd (kmul x y) (kmul x z)) /\
        kinv kzero = kzero /\
        (!x. x <> kzero ==> kmul (kinv x) x = kone))
      in
      let univariate_eval =
        \(coeffs : 'k list) (x : 'k).
          FOLDR (\c acc. kadd c (kmul x acc)) kzero coeffs
      in
      let algebraically_closed =
        !coeffs : 'k list.
          1 < LENGTH coeffs /\ LAST coeffs <> kzero
          ==>
          ?x : 'k. univariate_eval coeffs x = kzero
      in
      let is_polynomial =
        \q : ('i -> num) -> 'k.
          FINITE {m | q m <> kzero}
      in
      let polynomial_zero =
        \m : 'i -> num. kzero
      in
      let polynomial_add =
        \(q : ('i -> num) -> 'k) r m.
          kadd (q m) (r m)
      in
      let polynomial_neg =
        \(q : ('i -> num) -> 'k) m.
          kneg (q m)
      in
      let coefficient_decompositions =
        \(q : ('i -> num) -> 'k) r (m : 'i -> num).
          {ab |
             q (FST ab) <> kzero /\
             r (SND ab) <> kzero /\
             !i. FST ab i + SND ab i = m i}
      in
      let polynomial_mul =
        \(q : ('i -> num) -> 'k) r m.
          ITSET
            (\ab acc.
               kadd (kmul (q (FST ab)) (r (SND ab))) acc)
            (coefficient_decompositions q r m) kzero
      in
      let monomial_value =
        \(x : 'i -> 'k) (m : 'i -> num).
          ITSET
            (\i acc.
               kmul (FUNPOW (kmul (x i)) (m i) kone) acc)
            (UNIV : 'i set) kone
      in
      let polynomial_eval =
        \(x : 'i -> 'k) (q : ('i -> num) -> 'k).
          ITSET
            (\m acc. kadd (kmul (q m) (monomial_value x m)) acc)
            {m | q m <> kzero} kzero
      in
      let is_ideal =
        ((!q. I q ==> is_polynomial q) /\
        I polynomial_zero /\
        (!q r. I q /\ I r ==> I (polynomial_add q r)) /\
        (!q. I q ==> I (polynomial_neg q)) /\
        (!q r.
           I q /\ is_polynomial r ==> I (polynomial_mul q r)))
      in
      let zero_locus =
        \x : 'i -> 'k.
          !q. I q ==> polynomial_eval x q = kzero
      in
      let polynomial_map =
        \x : 'i -> 'k.
          \i. polynomial_eval x (p i)
      in
      let maps_to =
        !x. zero_locus x ==> zero_locus (polynomial_map x)
      in
      let injective_on =
        !x y.
          zero_locus x /\
          zero_locus y /\
          polynomial_map x = polynomial_map y
          ==>
          x = y
      in
      let surjective_on =
        !y.
          zero_locus y
          ==>
          ?x.
            zero_locus x /\
            polynomial_map x = y
      in
        field_axioms /\
        algebraically_closed /\
        FINITE (UNIV : 'i set) /\
        is_ideal /\
        (!i. is_polynomial (p i))
        ==>
        maps_to ==>
        injective_on ==>
        surjective_on``;
