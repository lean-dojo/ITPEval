-- Statement-only formalization of PutnamBench corpus artifact putnam_1969_a1:
-- the possible ranges of real bivariate polynomials are exactly the singletons,
-- four one-sided intervals, and the whole real line. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor truth

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedField (R : Set) : Set1 where
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
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

record Monomial (R : Set) : Set where
  constructor monomial
  field
    coefficient : R
    x-exponent  : Nat
    y-exponent  : Nat

open Monomial

Polynomial : Set -> Set
Polynomial R = List (Monomial R)

power :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals x (power reals x n)

evaluateMonomial :
  {R : Set} ->
  CompleteOrderedField R ->
  Monomial R ->
  R ->
  R ->
  R
evaluateMonomial reals term x y =
  multiply reals
    (coefficient term)
    (multiply reals
      (power reals x (x-exponent term))
      (power reals y (y-exponent term)))

evaluate :
  {R : Set} ->
  CompleteOrderedField R ->
  Polynomial R ->
  R ->
  R ->
  R
evaluate reals [] x y =
  zeroR reals
evaluate reals (term ∷ terms) x y =
  add reals
    (evaluateMonomial reals term x y)
    (evaluate reals terms x y)

module Putnam1969A1Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  Subset : Set1
  Subset = R -> Set

  SetEqual : Subset -> Subset -> Set
  SetEqual A B =
    (z : R) -> Iff (A z) (B z)

  StrictLess : R -> R -> Set
  StrictLess x y =
    lessOrEqual reals x y and x != y

  PolynomialRange : Polynomial R -> Subset
  PolynomialRange polynomial z =
    Exists R
      (\ x ->
        Exists R
          (\ y ->
            evaluate reals polynomial x y == z))

  HasPolynomialRange : Subset -> Set
  HasPolynomialRange S =
    Exists (Polynomial R)
      (\ polynomial ->
        SetEqual S (PolynomialRange polynomial))

  Singleton : R -> Subset
  Singleton endpoint z =
    z == endpoint

  ClosedAbove : R -> Subset
  ClosedAbove endpoint z =
    lessOrEqual reals endpoint z

  ClosedBelow : R -> Subset
  ClosedBelow endpoint z =
    lessOrEqual reals z endpoint

  OpenAbove : R -> Subset
  OpenAbove endpoint z =
    StrictLess endpoint z

  OpenBelow : R -> Subset
  OpenBelow endpoint z =
    StrictLess z endpoint

  Universal : Subset
  Universal z =
    Top

  ClassifiedRange : Subset -> Set
  ClassifiedRange S =
    Exists R
      (\ endpoint ->
        SetEqual S (Singleton endpoint)
        or
        SetEqual S (ClosedAbove endpoint)
        or
        SetEqual S (ClosedBelow endpoint)
        or
        SetEqual S (OpenAbove endpoint)
        or
        SetEqual S (OpenBelow endpoint))
    or
    SetEqual S Universal

  proposition : Set1
  proposition =
    (S : Subset) ->
    Iff
      (HasPolynomialRange S)
      (ClassifiedRange S)

putnam-1969-a1 : Set1
putnam-1969-a1 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1969A1Statement.proposition reals
