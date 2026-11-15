-- Statement-only formalization of PutnamBench corpus artifact putnam_1979_b6:
-- the real-part bound for the principal square root of a finite sum of
-- squares of complex numbers. This file contains no proof.

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

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ = y
... | right _ = x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

sumFirst :
  {A : Set} ->
  A ->
  (A -> A -> A) ->
  Nat ->
  (Nat -> A) ->
  A
sumFirst identity combine zero term =
  identity
sumFirst identity combine (suc n) term =
  combine
    (sumFirst identity combine n term)
    (term n)

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
    (add reals
      (multiply reals (realPart z) (realPart w))
      (negate reals
        (multiply reals (imaginaryPart z) (imaginaryPart w))))
    (add reals
      (multiply reals (realPart z) (imaginaryPart w))
      (multiply reals (imaginaryPart z) (realPart w)))

complexSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexSquare reals z =
  complexMultiply reals z z

record StandardComplexSquareRoot
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    principalSquareRoot : Complex R -> Complex R

    principal-square-root-square :
      (z : Complex R) ->
      complexSquare reals (principalSquareRoot z) == z

    principal-square-root-real-nonnegative :
      (z : Complex R) ->
      lessOrEqual reals
        (zeroR reals)
        (realPart (principalSquareRoot z))

    principal-square-root-branch-tie :
      (z : Complex R) ->
      realPart (principalSquareRoot z) == zeroR reals ->
      lessOrEqual reals
        (zeroR reals)
        (imaginaryPart (principalSquareRoot z))

open StandardComplexSquareRoot

module Putnam1979B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (roots : StandardComplexSquareRoot reals) where

  sumOfSquares :
    Nat ->
    (Nat -> Complex R) ->
    Complex R
  sumOfSquares n z =
    sumFirst
      (complexZero reals)
      (complexAdd reals)
      n
      (\ i -> complexSquare reals (z i))

  sumOfAbsoluteRealParts :
    Nat ->
    (Nat -> Complex R) ->
    R
  sumOfAbsoluteRealParts n z =
    sumFirst
      (zeroR reals)
      (add reals)
      n
      (\ i -> absoluteValue reals (realPart (z i)))

  proposition : Set
  proposition =
    (n : Nat) ->
    (z : Nat -> Complex R) ->
    lessOrEqual reals
      (absoluteValue reals
        (realPart
          (principalSquareRoot roots (sumOfSquares n z))))
      (sumOfAbsoluteRealParts n z)

putnam-1979-b6 : Set1
putnam-1979-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (roots : StandardComplexSquareRoot reals) ->
  Putnam1979B6Statement.proposition reals roots
