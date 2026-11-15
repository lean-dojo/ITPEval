-- Statement-only formalization of PutnamBench corpus artifact putnam_1971_a2:
-- the real polynomials satisfying P(0) = 0 and
-- P(x^2 + 1) = P(x)^2 + 1 for every real x are exactly the identity
-- polynomial. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_

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

open CompleteOrderedRealField

module PolynomialDefinitions
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Polynomial : Set
  Polynomial =
    List R

  coefficient : Polynomial -> Nat -> R
  coefficient [] n =
    zeroR reals
  coefficient (c ∷ coefficients) zero =
    c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  PolynomialEqual : Polynomial -> Polynomial -> Set
  PolynomialEqual p q =
    (n : Nat) -> coefficient p n == coefficient q n

  evaluate : Polynomial -> R -> R
  evaluate [] x =
    zeroR reals
  evaluate (c ∷ coefficients) x =
    add reals c
      (multiply reals x (evaluate coefficients x))

  X : Polynomial
  X =
    zeroR reals ∷ oneR reals ∷ []

  Solution : Polynomial -> Set
  Solution polynomial =
    PolynomialEqual polynomial X

  SatisfiesEquation : Polynomial -> Set
  SatisfiesEquation polynomial =
    evaluate polynomial (zeroR reals) == zeroR reals
    and
    ((x : R) ->
      evaluate polynomial
        (add reals
          (multiply reals x x)
          (oneR reals))
      ==
      add reals
        (multiply reals
          (evaluate polynomial x)
          (evaluate polynomial x))
        (oneR reals))

  proposition : Set
  proposition =
    (polynomial : Polynomial) ->
    Iff
      (SatisfiesEquation polynomial)
      (Solution polynomial)

putnam-1971-a2 : Set1
putnam-1971-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  PolynomialDefinitions.proposition reals
