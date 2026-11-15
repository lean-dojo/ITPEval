(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527219 (thousand-theorems__hol4__Q3527219), "Weierstrass preparation
  theorem": a formal power series over a commutative local ring complete in
  its maximal-ideal adic topology and nonzero modulo that ideal factors as a
  distinguished polynomial times a unit power series. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val q3527219_comm_ring_def = new_definition (
  "q3527219_comm_ring_def",
  ``q3527219_comm_ring
      (zero : 'a) (oneR : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul oneR x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z))``);

val q3527219_ideal_def = new_definition (
  "q3527219_ideal_def",
  ``q3527219_ideal
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (mul : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (ideal : 'a -> bool) <=>
      ideal zero /\
      (!x y. ideal x /\ ideal y ==> ideal (add x y)) /\
      (!x. ideal x ==> ideal (neg x)) /\
      (!a x. ideal x ==> ideal (mul a x))``);

val q3527219_unit_def = new_definition (
  "q3527219_unit_def",
  ``q3527219_unit
      (oneR : 'a) (mul : 'a -> 'a -> 'a) (x : 'a) <=>
      ?y : 'a. mul x y = oneR``);

val q3527219_local_ring_def = new_definition (
  "q3527219_local_ring_def",
  ``q3527219_local_ring
      (zero : 'a) (oneR : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (maximal : 'a -> bool) <=>
      q3527219_ideal zero add mul neg maximal /\
      ~maximal oneR /\
      (!x. ~maximal x ==> q3527219_unit oneR mul x)``);

val q3527219_ideal_pow_def = new_definition (
  "q3527219_ideal_pow_def",
  ``q3527219_ideal_pow
      (zero : 'a) (oneR : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (ideal : 'a -> bool) (n : num) (x : 'a) <=>
      ?terms : ('a # 'a list) list.
        x =
          FOLDL add zero
            (MAP
              (\term.
                mul (FST term)
                  (FOLDL mul oneR (SND term)))
              terms) /\
        EVERY
          (\term.
            LENGTH (SND term) = n /\
            EVERY ideal (SND term))
          terms``);

val q3527219_adic_complete_def = new_definition (
  "q3527219_adic_complete_def",
  ``q3527219_adic_complete
      (zero : 'a) (oneR : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (ideal : 'a -> bool) <=>
      (!x.
        (!n. q3527219_ideal_pow zero oneR add mul ideal n x)
        ==>
        x = zero) /\
      (!f : num -> 'a.
        (!m n.
          m <= n
          ==>
          q3527219_ideal_pow zero oneR add mul ideal m
            (add (f m) (neg (f n))))
        ==>
        ?limit : 'a.
          !n.
            q3527219_ideal_pow zero oneR add mul ideal n
              (add (f n) (neg limit)))``);

val q3527219_series_one_def = new_definition (
  "q3527219_series_one_def",
  ``q3527219_series_one (zero : 'a) (oneR : 'a) =
      (\n : num. if n = 0 then oneR else zero)``);

val q3527219_series_mul_def = new_definition (
  "q3527219_series_mul_def",
  ``q3527219_series_mul
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (mul : 'a -> 'a -> 'a)
      (f : num -> 'a) (g : num -> 'a) =
      (\n : num.
        FOLDL add zero
          (GENLIST (\i. mul (f i) (g (n - i))) (SUC n)))``);

val q3527219_distinguished_def = new_definition (
  "q3527219_distinguished_def",
  ``q3527219_distinguished
      (zero : 'a) (oneR : 'a)
      (maximal : 'a -> bool) (p : num -> 'a) <=>
      ?d : num.
        p d = oneR /\
        (!n. d < n ==> p n = zero) /\
        (!n. n < d ==> maximal (p n))``);

val q3527219_series_unit_def = new_definition (
  "q3527219_series_unit_def",
  ``q3527219_series_unit
      (zero : 'a) (oneR : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (h : num -> 'a) <=>
      ?u : num -> 'a.
        q3527219_series_mul zero add mul h u =
        q3527219_series_one zero oneR``);

val exists_isWeierstrassFactorization =
  ``!(zero : 'a) (oneR : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (maximal : 'a -> bool)
      (g : num -> 'a).
      q3527219_comm_ring zero oneR add mul neg /\
      q3527219_local_ring zero oneR add mul neg maximal /\
      q3527219_adic_complete zero oneR add mul neg maximal /\
      (?n : num. ~maximal (g n))
      ==>
      ?p h : num -> 'a.
        q3527219_distinguished zero oneR maximal p /\
        q3527219_series_unit zero oneR add mul h /\
        g = q3527219_series_mul zero add mul p h``;
