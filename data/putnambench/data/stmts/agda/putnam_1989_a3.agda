-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_a3:
-- every complex zero of 11 z^10 + 10 i z^9 + 10 i z - 11 has modulus one.
-- This file contains no proof.

{-# OPTIONS --safe #-}

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

embedNatural :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Complex R
embedNatural reals n =
  complex (fromNat reals n) (zeroR reals)

imaginaryUnit :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
imaginaryUnit reals =
  complex (zeroR reals) (oneR reals)

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

complexNegate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexNegate reals z =
  complex
    (negate reals (realPart z))
    (negate reals (imaginaryPart z))

complexSubtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexSubtract reals z w =
  complexAdd reals z (complexNegate reals w)

complexMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals z w =
  complex
    (add reals
      (multiply reals (realPart z) (realPart w))
      (negate reals
        (multiply reals (imaginaryPart z) (imaginaryPart w))))
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
complexPower reals z (suc exponent) =
  complexMultiply reals
    (complexPower reals z exponent)
    z

complexSquaredModulus :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexSquaredModulus reals z =
  add reals
    (multiply reals (realPart z) (realPart z))
    (multiply reals (imaginaryPart z) (imaginaryPart z))

complexModulus :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexModulus reals z =
  squareRoot reals (complexSquaredModulus reals z)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

sixN : Nat
sixN =
  suc fiveN

sevenN : Nat
sevenN =
  suc sixN

eightN : Nat
eightN =
  suc sevenN

nineN : Nat
nineN =
  suc eightN

tenN : Nat
tenN =
  suc nineN

elevenN : Nat
elevenN =
  suc tenN

module Putnam1989A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  tenI : Complex R
  tenI =
    complexMultiply reals
      (embedNatural reals tenN)
      (imaginaryUnit reals)

  polynomialValue : Complex R -> Complex R
  polynomialValue z =
    complexSubtract reals
      (complexAdd reals
        (complexAdd reals
          (complexMultiply reals
            (embedNatural reals elevenN)
            (complexPower reals z tenN))
          (complexMultiply reals
            tenI
            (complexPower reals z nineN)))
        (complexMultiply reals tenI z))
      (embedNatural reals elevenN)

  proposition : Set
  proposition =
    (z : Complex R) ->
    polynomialValue z == complexZero reals ->
    complexModulus reals z == oneR reals

putnam-1989-a3 : Set1
putnam-1989-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1989A3Statement.proposition reals
