-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_a2
-- (putnambench__agda__putnam_2024_a2): the real polynomials satisfying the
-- given composition and divisibility identity are exactly the affine
-- polynomials with slope 1 or -1. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2024A2 where

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

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

Polynomial : Set -> Set
Polynomial R =
  List R

coefficient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Nat ->
  R
coefficient reals [] n =
  zeroR reals
coefficient reals (c ∷ coefficients) zero =
  c
coefficient reals (c ∷ coefficients) (suc n) =
  coefficient reals coefficients n

PolynomialEqual :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Set
PolynomialEqual reals p q =
  (n : Nat) ->
  coefficient reals p n == coefficient reals q n

evaluate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluate reals [] x =
  zeroR reals
evaluate reals (c ∷ coefficients) x =
  add reals c
    (multiply reals x (evaluate reals coefficients x))

SatisfiesIdentity :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Set
SatisfiesIdentity {R} reals p =
  Exists (Polynomial R)
    (\ q ->
      (x : R) ->
      subtract reals
        (evaluate reals p (evaluate reals p x))
        x
      ==
      multiply reals
        (square reals
          (subtract reals (evaluate reals p x) x))
        (evaluate reals q x))

AffineWithUnitIntegerSlope :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Set
AffineWithUnitIntegerSlope {R} reals p =
  Exists R
    (\ constant ->
      PolynomialEqual reals p
        (constant ∷ oneR reals ∷ [])
      or
      PolynomialEqual reals p
        (constant ∷ negate reals (oneR reals) ∷ []))

putnam-2024-a2 : Set1
putnam-2024-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (p : Polynomial R) ->
  Iff
    (SatisfiesIdentity reals p)
    (AffineWithUnitIntegerSlope reals p)
