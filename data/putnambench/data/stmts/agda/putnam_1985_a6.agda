-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_a6:
-- the real polynomials 3x^2 + 7x + 2 and 6x^2 + 5x + 1 have equal sums of
-- squared coefficients in every positive power, and the latter has value one
-- at zero. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

Polynomial : Set -> Set
Polynomial R =
  List R

addPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
addPolynomial reals [] q =
  q
addPolynomial reals p [] =
  p
addPolynomial reals (a ∷ p) (b ∷ q) =
  add reals a b ∷ addPolynomial reals p q

scalePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Polynomial R ->
  Polynomial R
scalePolynomial reals c [] =
  []
scalePolynomial reals c (a ∷ p) =
  multiply reals c a ∷ scalePolynomial reals c p

multiplyPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
multiplyPolynomial reals [] q =
  []
multiplyPolynomial reals (a ∷ p) q =
  addPolynomial reals
    (scalePolynomial reals a q)
    (zeroR reals ∷ multiplyPolynomial reals p q)

powerPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Nat ->
  Polynomial R
powerPolynomial reals p zero =
  oneR reals ∷ []
powerPolynomial reals p (suc n) =
  multiplyPolynomial reals p (powerPolynomial reals p n)

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluatePolynomial reals [] x =
  zeroR reals
evaluatePolynomial reals (a ∷ p) x =
  add reals a
    (multiply reals x (evaluatePolynomial reals p x))

coefficientSquareSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R
coefficientSquareSum reals [] =
  zeroR reals
coefficientSquareSum reals (a ∷ p) =
  add reals
    (multiply reals a a)
    (coefficientSquareSum reals p)

module Putnam1985A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  f : Polynomial R
  f =
    fromNat reals 2 ∷
    fromNat reals 7 ∷
    fromNat reals 3 ∷
    []

  g : Polynomial R
  g =
    fromNat reals 1 ∷
    fromNat reals 5 ∷
    fromNat reals 6 ∷
    []

  Gamma : Polynomial R -> R
  Gamma =
    coefficientSquareSum reals

  proposition : Set
  proposition =
    evaluatePolynomial reals g (zeroR reals) == oneR reals
    and
    ((n : Nat) ->
      Positive n ->
      Gamma (powerPolynomial reals f n)
      ==
      Gamma (powerPolynomial reals g n))

putnam-1985-a6 : Set1
putnam-1985-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1985A6Statement.proposition reals
