(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1068976, "Hilbert's Nullstellensatz": over an algebraically closed field
  extension and finitely many variables, the ideal vanishing on an ideal's
  zero locus is its radical. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pairTheory pred_setTheory;

val q1068976_field_def = new_definition (
  "q1068976_field_def",
  ``q1068976_field
      (z : 'a) (u : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (invop : 'a -> 'a) <=>
      z <> u /\
      (!x. add z x = x) /\
      (!x. add (neg x) x = z) /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. mul u x = x) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y z.
         mul x (add y z) = add (mul x y) (mul x z)) /\
      (!x. x <> z ==> mul (invop x) x = u)``);

val hilberts_nullstellensatz =
  ``!(vars : 'v set)
      (k0 : 'k) (k1 : 'k)
      (kadd : 'k -> 'k -> 'k)
      (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k)
      (kinv : 'k -> 'k)
      (K0 : 'K) (K1 : 'K)
      (Kadd : 'K -> 'K -> 'K)
      (Kmul : 'K -> 'K -> 'K)
      (Kneg : 'K -> 'K)
      (Kinv : 'K -> 'K)
      (embed : 'k -> 'K).
      let is_embedding =
        (embed k0 = K0 /\
         embed k1 = K1 /\
         (!x y. embed (kadd x y) = Kadd (embed x) (embed y)) /\
         (!x y. embed (kmul x y) = Kmul (embed x) (embed y)))
      in
      let K_is_algebraically_closed =
        !coeffs : 'K list.
          1 < LENGTH coeffs /\ LAST coeffs <> K0
          ==>
          ?x : 'K.
            FOLDR (\c acc. Kadd c (Kmul x acc)) K0 coeffs = K0
      in
      let is_monomial =
        \m : 'v -> num.
          FINITE {v | m v <> 0} /\
          {v | m v <> 0} SUBSET vars
      in
      let is_polynomial =
        \p : ('v -> num) -> 'k.
          FINITE {m | p m <> k0} /\
          !m. p m <> k0 ==> is_monomial m
      in
      let polynomial_zero =
        \m : 'v -> num. k0
      in
      let polynomial_one =
        \m : 'v -> num.
          if (!v. m v = 0) then k1 else k0
      in
      let polynomial_add =
        \(p : ('v -> num) -> 'k) q m.
          kadd (p m) (q m)
      in
      let polynomial_neg =
        \(p : ('v -> num) -> 'k) m.
          kneg (p m)
      in
      let decompositions =
        \m : 'v -> num.
          {(a,b) |
             is_monomial a /\
             is_monomial b /\
             !v. a v + b v = m v}
      in
      let polynomial_mul =
        \(p : ('v -> num) -> 'k) q m.
          ITSET
            (\ab acc.
               kadd (kmul (p (FST ab)) (q (SND ab))) acc)
            (decompositions m) k0
      in
      let polynomial_pow =
        \(p : ('v -> num) -> 'k) n.
          FUNPOW (polynomial_mul p) n polynomial_one
      in
      let monomial_value =
        \(x : 'v -> 'K) (m : 'v -> num).
          ITSET
            (\v acc.
               Kmul (FUNPOW (Kmul (x v)) (m v) K1) acc)
            vars K1
      in
      let polynomial_eval =
        \(x : 'v -> 'K) (p : ('v -> num) -> 'k).
          ITSET
            (\m acc.
               Kadd (Kmul (embed (p m)) (monomial_value x m)) acc)
            {m | p m <> k0} K0
      in
      let is_ideal =
        \I : ((('v -> num) -> 'k) -> bool).
          (!p. I p ==> is_polynomial p) /\
          I polynomial_zero /\
          (!p q. I p /\ I q ==> I (polynomial_add p q)) /\
          (!p. I p ==> I (polynomial_neg p)) /\
          (!p q.
             I p /\ is_polynomial q ==> I (polynomial_mul p q))
      in
        FINITE vars /\
        q1068976_field k0 k1 kadd kmul kneg kinv /\
        q1068976_field K0 K1 Kadd Kmul Kneg Kinv /\
        is_embedding /\
        K_is_algebraically_closed
        ==>
        !I : ((('v -> num) -> 'k) -> bool).
          is_ideal I
          ==>
          !p : ('v -> num) -> 'k.
            is_polynomial p
            ==>
            ((!x : 'v -> 'K.
                (!q. I q ==> polynomial_eval x q = K0)
                ==>
                polynomial_eval x p = K0)
             <=>
             ?n : num. I (polynomial_pow p n))``;
