-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_a1
-- (putnambench__agda__putnam_2007_a1): the real parameters for which the two
-- mutually defined quadratic curves are tangent are exactly the stated four
-- values. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2007A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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
    negate inverse squareRoot : R -> R
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
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

fraction :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  R
fraction reals numerator denominator =
  divide reals
    (fromNat reals numerator)
    (fromNat reals denominator)

quadratic :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
quadratic reals alpha t =
  add reals
    (add reals
      (multiply reals alpha (square reals t))
      (multiply reals alpha t))
    (fraction reals 1 24)

quadraticDerivative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
quadraticDerivative reals alpha t =
  add reals
    (multiply reals
      (multiply reals (fromNat reals 2) alpha)
      t)
    alpha

TangentQuadraticCurves :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
TangentQuadraticCurves {R} reals alpha =
  Exists R
    (\ x ->
      Exists R
        (\ y ->
          quadratic reals alpha x == y
          and
          quadratic reals alpha y == x
          and
          multiply reals
            (quadraticDerivative reals alpha x)
            (quadraticDerivative reals alpha y)
          == oneR reals))

Putnam2007A1Solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Putnam2007A1Solution reals alpha =
  alpha == fraction reals 2 3
  or
  alpha == fraction reals 3 2
  or
  alpha ==
    divide reals
      (add reals
        (fromNat reals 13)
        (squareRoot reals (fromNat reals 601)))
      (fromNat reals 12)
  or
  alpha ==
    divide reals
      (subtract reals
        (fromNat reals 13)
        (squareRoot reals (fromNat reals 601)))
      (fromNat reals 12)

putnam-2007-a1 : Set1
putnam-2007-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (alpha : R) ->
  Iff
    (TangentQuadraticCurves reals alpha)
    (Putnam2007A1Solution reals alpha)
