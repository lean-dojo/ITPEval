-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_b5
-- (putnambench__agda__putnam_2020_b5): four unit-modulus complex numbers
-- distinct from one make the specified symmetric polynomial nonzero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2020B5 where

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

-- Complete Archimedean ordered fields are unique up to ordered-field
-- isomorphism, so this structurally presents the standard real numbers.
record CompleteArchimedeanOrderedField (R : Set) : Set1 where
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

open CompleteArchimedeanOrderedField

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexFromNat :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Nat ->
  Complex R
complexFromNat reals n =
  complex (fromNat reals n) (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals z w =
  complex
    (add reals (realPart z) (realPart w))
    (add reals (imaginaryPart z) (imaginaryPart w))

complexNegate :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R ->
  Complex R
complexNegate reals z =
  complex
    (negate reals (realPart z))
    (negate reals (imaginaryPart z))

complexSubtract :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexSubtract reals z w =
  complexAdd reals z (complexNegate reals w)

complexMultiply :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
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

complexNormSquared :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R ->
  R
complexNormSquared reals z =
  add reals
    (multiply reals (realPart z) (realPart z))
    (multiply reals (imaginaryPart z) (imaginaryPart z))

UnitModulus :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R ->
  Set
UnitModulus reals z =
  complexNormSquared reals z == oneR reals

putnamExpression :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R ->
  Complex R ->
  Complex R
putnamExpression reals z1 z2 z3 z4 =
  complexAdd reals
    (complexSubtract reals
      (complexSubtract reals
        (complexSubtract reals
          (complexSubtract reals
            (complexFromNat reals 3)
            z1)
          z2)
        z3)
      z4)
    (complexMultiply reals
      (complexMultiply reals
        (complexMultiply reals z1 z2)
        z3)
      z4)

putnam-2020-b5 : Set1
putnam-2020-b5 =
  (R : Set) ->
  (reals : CompleteArchimedeanOrderedField R) ->
  (z1 z2 z3 z4 : Complex R) ->
  UnitModulus reals z1 ->
  UnitModulus reals z2 ->
  UnitModulus reals z3 ->
  UnitModulus reals z4 ->
  z1 != complexOne reals ->
  z2 != complexOne reals ->
  z3 != complexOne reals ->
  z4 != complexOne reals ->
  putnamExpression reals z1 z2 z3 z4 != complexZero reals
