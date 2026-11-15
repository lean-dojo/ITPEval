-- Statement-only formalization of Thousand Theorems corpus artifact Q570779,
-- "Vieta's formulas": over any commutative semiring, the product of the linear
-- polynomials X + C(r) is the sum determined by the elementary symmetric
-- functions of the multiset of coefficients. This file contains no proof.

{-# OPTIONS --safe #-}

module Q570779_vieta_s_formulas where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

record CommutativeSemiring
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-zero-left :
      (x : R) ->
      addR zeroR x == x
    add-zero-right :
      (x : R) ->
      addR x zeroR == x

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-one-left :
      (x : R) ->
      multiplyR oneR x == x
    multiply-one-right :
      (x : R) ->
      multiplyR x oneR == x

    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ==
      addR (multiplyR x z) (multiplyR y z)
    multiply-zero-left :
      (x : R) ->
      multiplyR zeroR x == zeroR
    multiply-zero-right :
      (x : R) ->
      multiplyR x zeroR == zeroR

Polynomial :
  {r : Level} ->
  Set r ->
  Set r
Polynomial R =
  List R

coefficient :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Polynomial R ->
  Nat ->
  R
coefficient semiring [] n =
  CommutativeSemiring.zeroR semiring
coefficient semiring (a ∷ coefficients) zero =
  a
coefficient semiring (a ∷ coefficients) (suc n) =
  coefficient semiring coefficients n

PolynomialEquality :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Polynomial R ->
  Polynomial R ->
  Set r
PolynomialEquality semiring p q =
  (n : Nat) ->
  coefficient semiring p n == coefficient semiring q n

addPolynomial :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
addPolynomial semiring [] q =
  q
addPolynomial semiring p [] =
  p
addPolynomial semiring (a ∷ p) (b ∷ q) =
  CommutativeSemiring.addR semiring a b ∷
  addPolynomial semiring p q

scalePolynomial :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  R ->
  Polynomial R ->
  Polynomial R
scalePolynomial semiring a [] =
  []
scalePolynomial semiring a (b ∷ p) =
  CommutativeSemiring.multiplyR semiring a b ∷
  scalePolynomial semiring a p

multiplyPolynomial :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
multiplyPolynomial semiring [] q =
  []
multiplyPolynomial semiring (a ∷ p) q =
  addPolynomial semiring
    (scalePolynomial semiring a q)
    (CommutativeSemiring.zeroR semiring ∷
      multiplyPolynomial semiring p q)

constantPolynomial :
  {r : Level}
  {R : Set r} ->
  R ->
  Polynomial R
constantPolynomial a =
  a ∷ []

xPolynomial :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Polynomial R
xPolynomial semiring =
  CommutativeSemiring.zeroR semiring ∷
  CommutativeSemiring.oneR semiring ∷
  []

onePolynomial :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Polynomial R
onePolynomial semiring =
  constantPolynomial (CommutativeSemiring.oneR semiring)

powerPolynomial :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Polynomial R ->
  Nat ->
  Polynomial R
powerPolynomial semiring p zero =
  onePolynomial semiring
powerPolynomial semiring p (suc n) =
  multiplyPolynomial semiring
    (powerPolynomial semiring p n)
    p

linearPolynomial :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  R ->
  Polynomial R
linearPolynomial semiring a =
  addPolynomial semiring
    (xPolynomial semiring)
    (constantPolynomial a)

productOfLinearPolynomials :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  List R ->
  Polynomial R
productOfLinearPolynomials semiring [] =
  onePolynomial semiring
productOfLinearPolynomials semiring (a ∷ coefficients) =
  multiplyPolynomial semiring
    (linearPolynomial semiring a)
    (productOfLinearPolynomials semiring coefficients)

length :
  {r : Level}
  {R : Set r} ->
  List R ->
  Nat
length [] =
  zero
length (x ∷ xs) =
  suc (length xs)

elementarySymmetric :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  List R ->
  Nat ->
  R
elementarySymmetric semiring [] zero =
  CommutativeSemiring.oneR semiring
elementarySymmetric semiring [] (suc k) =
  CommutativeSemiring.zeroR semiring
elementarySymmetric semiring (x ∷ xs) zero =
  CommutativeSemiring.oneR semiring
elementarySymmetric semiring (x ∷ xs) (suc k) =
  CommutativeSemiring.addR semiring
    (elementarySymmetric semiring xs (suc k))
    (CommutativeSemiring.multiplyR semiring x
      (elementarySymmetric semiring xs k))

sumThrough :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Nat ->
  (Nat -> Polynomial R) ->
  Polynomial R
sumThrough semiring zero terms =
  terms zero
sumThrough semiring (suc n) terms =
  addPolynomial semiring
    (sumThrough semiring n terms)
    (terms (suc n))

vieta-s-formulas : Setω
vieta-s-formulas =
  {r : Level} ->
  (R : Set r) ->
  (semiring : CommutativeSemiring R) ->
  (coefficients : List R) ->
  PolynomialEquality semiring
    (productOfLinearPolynomials semiring coefficients)
    (sumThrough semiring (length coefficients)
      (\ j ->
        multiplyPolynomial semiring
          (constantPolynomial
            (elementarySymmetric semiring coefficients j))
          (powerPolynomial semiring
            (xPolynomial semiring)
            (length coefficients - j))))
