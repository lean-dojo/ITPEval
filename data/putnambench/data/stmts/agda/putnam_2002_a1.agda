-- Statement-only formalization of PutnamBench corpus artifact putnam_2002_a1
-- (putnambench__agda__putnam_2002_a1): the numerator polynomial in the nth
-- derivative of 1 / (x^k - 1) has value (-k)^n n! at one. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2002A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<N_
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

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse absoluteValue : R -> R
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

    absolute-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (absoluteValue x)
    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValue x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValue x == negate x

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

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals (naturalPower reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

record Polynomial
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set where
  constructor polynomial
  field
    coefficient : Nat -> R
    degreeBound : Nat
    zeroAbove :
      (n : Nat) ->
      degreeBound <N n ->
      coefficient n == zeroR reals

open Polynomial

evaluate :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  R ->
  R
evaluate reals polynomialValue x =
  sumFirst reals
    (suc (degreeBound polynomialValue))
    (\ i ->
      multiply reals
        (coefficient polynomialValue i)
        (naturalPower reals x i))

HasDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
HasDerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((increment : R) ->
        StrictLess reals
          (absoluteValue reals increment)
          delta ->
        increment != zeroR reals ->
        StrictLess reals
          (absoluteValue reals
            (subtract reals
              (divide reals
                (subtract reals
                  (function (add reals point increment))
                  (function point))
                increment)
              derivative))
          epsilon))

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivative =
  HasDerivativeAt reals function point derivative
  or
  (Not
    (Exists R
      (\ value ->
        HasDerivativeAt reals function point value))
  and
  derivative == zeroR reals)

IteratedDerivativeValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (R -> R) ->
  R ->
  R ->
  Set
IteratedDerivativeValue reals zero function point value =
  value == function point
IteratedDerivativeValue {R} reals (suc n) function point value =
  Exists (R -> R)
    (\ derivativeFunction ->
      ((x : R) ->
        DerivativeAt reals function x (derivativeFunction x))
      and
      IteratedDerivativeValue reals n derivativeFunction point value)

putnamFunction :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R ->
  R
putnamFunction reals k x =
  divide reals
    (oneR reals)
    (subtract reals
      (naturalPower reals x k)
      (oneR reals))

derivativeNumeratorQuotient :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Nat ->
  Polynomial reals ->
  Nat ->
  R ->
  R
derivativeNumeratorQuotient reals k polynomialValue n x =
  divide reals
    (evaluate reals polynomialValue x)
    (naturalPower reals
      (subtract reals
        (naturalPower reals x k)
        (oneR reals))
      (suc n))

putnamSolution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  R
putnamSolution reals k n =
  multiply reals
    (naturalPower reals
      (negate reals (fromNat reals k))
      n)
    (fromNat reals (factorial n))

putnam-2002-a1 : Set1
putnam-2002-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (k : Nat) ->
  (P : Nat -> Polynomial reals) ->
  zero <N k ->
  ((n : Nat) ->
    (x : R) ->
    IteratedDerivativeValue reals n
      (putnamFunction reals k)
      x
      (derivativeNumeratorQuotient reals k (P n) n x)) ->
  (n : Nat) ->
  evaluate reals (P n) (oneR reals) ==
    putnamSolution reals k n
