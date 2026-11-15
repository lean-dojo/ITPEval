-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_b5
-- (putnambench__agda__putnam_2005_b5): a harmonic real multivariate
-- polynomial divisible by the sum of the squares of its variables is
-- identically zero. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005B5 where

open import Agda.Builtin.Bool using (Bool; true; false)
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data PositiveNat : Nat -> Set where
  positive : {n : Nat} -> PositiveNat (suc n)

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

sameFin :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Bool
sameFin fzero fzero =
  true
sameFin fzero (fsuc j) =
  false
sameFin (fsuc i) fzero =
  false
sameFin (fsuc i) (fsuc j) =
  sameFin i j

choose :
  {A : Set} ->
  Bool ->
  A ->
  A ->
  A
choose true whenTrue whenFalse =
  whenTrue
choose false whenTrue whenFalse =
  whenFalse

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

power :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
power reals x zero =
  oneR reals
power reals x (suc exponent) =
  multiply reals x (power reals x exponent)

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} terms =
  zeroR reals
sumFin reals {suc n} terms =
  add reals
    (terms fzero)
    (sumFin reals (\ i -> terms (fsuc i)))

productFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
productFin reals {zero} terms =
  oneR reals
productFin reals {suc n} terms =
  multiply reals
    (terms fzero)
    (productFin reals (\ i -> terms (fsuc i)))

record Monomial (R : Set) (n : Nat) : Set where
  constructor monomial
  field
    coefficient : R
    exponents   : Fin n -> Nat

open Monomial

Polynomial : Set -> Nat -> Set
Polynomial R n =
  List (Monomial R n)

evaluateMonomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Monomial R n ->
  (Fin n -> R) ->
  R
evaluateMonomial reals term point =
  multiply reals
    (coefficient term)
    (productFin reals
      (\ i ->
        power reals
          (point i)
          (exponents term i)))

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Polynomial R n ->
  (Fin n -> R) ->
  R
evaluatePolynomial reals [] point =
  zeroR reals
evaluatePolynomial reals (term ∷ terms) point =
  add reals
    (evaluateMonomial reals term point)
    (evaluatePolynomial reals terms point)

lowerExponent :
  {n : Nat} ->
  Fin n ->
  (Fin n -> Nat) ->
  Fin n ->
  Nat
lowerExponent selected powers index =
  choose
    (sameFin selected index)
    (predecessor (powers index))
    (powers index)

differentiateMonomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Fin n ->
  Monomial R n ->
  Monomial R n
differentiateMonomial reals selected term =
  monomial
    (multiply reals
      (coefficient term)
      (fromNat reals (exponents term selected)))
    (lowerExponent selected (exponents term))

partialDerivative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Fin n ->
  Polynomial R n ->
  Polynomial R n
partialDerivative reals selected [] =
  []
partialDerivative reals selected (term ∷ terms) =
  differentiateMonomial reals selected term
  ∷ partialDerivative reals selected terms

PolynomialEqual :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Polynomial R n ->
  Polynomial R n ->
  Set
PolynomialEqual reals P Q =
  (point : _) ->
  evaluatePolynomial reals P point ==
  evaluatePolynomial reals Q point

Harmonic :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Polynomial R n ->
  Set
Harmonic reals P =
  (point : _) ->
  sumFin reals
    (\ i ->
      evaluatePolynomial reals
        (partialDerivative reals i
          (partialDerivative reals i P))
        point)
  ==
  zeroR reals

radiusSquared :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
radiusSquared reals point =
  sumFin reals
    (\ i ->
      multiply reals
        (point i)
        (point i))

RadiusSquaredDivides :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Polynomial R n ->
  Set
RadiusSquaredDivides {R} reals {n} P =
  Exists (Polynomial R n)
    (\ Q ->
      (point : Fin n -> R) ->
      multiply reals
        (radiusSquared reals point)
        (evaluatePolynomial reals Q point)
      ==
      evaluatePolynomial reals P point)

putnam-2005-b5 : Set1
putnam-2005-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  PositiveNat n ->
  (P : Polynomial R n) ->
  Harmonic reals P ->
  RadiusSquaredDivides reals P ->
  PolynomialEqual reals P []
