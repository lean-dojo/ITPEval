-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_a5
-- (putnambench__agda__putnam_2023_a5): the complex zeros of a finite
-- polynomial sum weighted by counts of ones in ternary expansions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper; mod-helper)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

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

record _iff_ (A B : Set) : Set where
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
      fromNat (m + n) ==
      add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) ==
      multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))
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

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  suc zero
naturalPower base (suc exponent) =
  naturalPower base exponent * base

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

oneIndicator : Nat -> Nat
oneIndicator zero =
  zero
oneIndicator (suc zero) =
  suc zero
oneIndicator (suc (suc n)) =
  zero

ternaryOneCountWithFuel : Nat -> Nat -> Nat
ternaryOneCountWithFuel zero n =
  zero
ternaryOneCountWithFuel (suc fuel) zero =
  zero
ternaryOneCountWithFuel (suc fuel) (suc n) =
  oneIndicator (naturalMod (suc n) 3) +
  ternaryOneCountWithFuel fuel (naturalDiv (suc n) 3)

ternaryOneCount : Nat -> Nat
ternaryOneCount zero =
  zero
ternaryOneCount (suc n) =
  ternaryOneCountWithFuel (suc n) (suc n)

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

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexFromNat :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Complex R
complexFromNat reals n =
  complex (fromNat reals n) (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals z w =
  complex
    (add reals (realPart z) (realPart w))
    (add reals (imaginaryPart z) (imaginaryPart w))

complexMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals z w =
  complex
    (subtract reals
      (multiply reals (realPart z) (realPart w))
      (multiply reals (imaginaryPart z) (imaginaryPart w)))
    (add reals
      (multiply reals (realPart z) (imaginaryPart w))
      (multiply reals (imaginaryPart z) (realPart w)))

complexPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Nat ->
  Complex R
complexPower reals z zero =
  complexOne reals
complexPower reals z (suc n) =
  complexMultiply reals (complexPower reals z n) z

record FiniteComplexSummation
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set where
  field
    sumFirst :
      Nat ->
      (Nat -> Complex R) ->
      Complex R

    sum-zero :
      (term : Nat -> Complex R) ->
      sumFirst zero term == complexZero reals

    sum-successor :
      (count : Nat) ->
      (term : Nat -> Complex R) ->
      sumFirst (suc count) term ==
      complexAdd reals
        (sumFirst count term)
        (term count)

open FiniteComplexSummation

module Putnam2023A5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (sums : FiniteComplexSummation reals) where

  threeTo1010 : Nat
  threeTo1010 =
    naturalPower 3 1010

  nineTo1010 : Nat
  nineTo1010 =
    naturalPower 9 1010

  minusTwo : Complex R
  minusTwo =
    complex
      (negate reals (fromNat reals 2))
      (zeroR reals)

  polynomialValue : Complex R -> Complex R
  polynomialValue z =
    sumFirst sums threeTo1010
      (\ k ->
        complexMultiply reals
          (complexPower reals minusTwo (ternaryOneCount k))
          (complexPower reals
            (complexAdd reals z (complexFromNat reals k))
            2023))

  center : R
  center =
    negate reals
      (divide reals
        (subtract reals
          (fromNat reals threeTo1010)
          (oneR reals))
        (fromNat reals 2))

  imaginaryOffset : R
  imaginaryOffset =
    divide reals
      (squareRoot reals
        (subtract reals
          (fromNat reals nineTo1010)
          (oneR reals)))
      (fromNat reals 4)

  ExplicitSolution : Complex R -> Set
  ExplicitSolution z =
    z == complex center (zeroR reals)
    or
    z == complex center imaginaryOffset
    or
    z == complex center (negate reals imaginaryOffset)

  proposition : Set
  proposition =
    (z : Complex R) ->
    (polynomialValue z == complexZero reals)
    iff
    ExplicitSolution z

putnam-2023-a5 : Set1
putnam-2023-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (sums : FiniteComplexSummation reals) ->
  Putnam2023A5Statement.proposition reals sums
