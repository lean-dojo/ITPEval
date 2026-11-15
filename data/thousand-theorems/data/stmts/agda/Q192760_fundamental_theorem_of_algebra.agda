-- Statement-only formalization of thousand-theorems corpus artifact Q192760
-- (thousand-theorems__agda__Q192760), "Fundamental theorem of algebra":
-- every nonconstant polynomial with complex coefficients has a complex root.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q192760_fundamental_theorem_of_algebra where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

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

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) ->
      addR x zeroR == x
    add-inverseR :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zeroR :
      inverseR zeroR == zeroR
    multiply-inverseR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexiveR :
      (x : R) ->
      lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open CompleteOrderedField

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

zeroC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
zeroC reals =
  complex (zeroR reals) (zeroR reals)

addC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
addC reals (complex a b) (complex c d) =
  complex
    (addR reals a c)
    (addR reals b d)

negateC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R
negateC reals (complex a b) =
  complex
    (negateR reals a)
    (negateR reals b)

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

multiplyC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
multiplyC reals (complex a b) (complex c d) =
  complex
    (subtractR reals
      (multiplyR reals a c)
      (multiplyR reals b d))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

Polynomial : Set -> Set
Polynomial R =
  List (Complex R)

evaluate :
  {R : Set} ->
  CompleteOrderedField R ->
  Polynomial R ->
  Complex R ->
  Complex R
evaluate reals [] z =
  zeroC reals
evaluate reals (coefficient ∷ coefficients) z =
  addC reals coefficient
    (multiplyC reals z (evaluate reals coefficients z))

data HasNonzeroCoefficient
  {R : Set}
  (reals : CompleteOrderedField R) :
  Polynomial R ->
  Set where

  here :
    {coefficient : Complex R} ->
    {coefficients : Polynomial R} ->
    coefficient != zeroC reals ->
    HasNonzeroCoefficient reals (coefficient ∷ coefficients)

  there :
    {coefficient : Complex R} ->
    {coefficients : Polynomial R} ->
    HasNonzeroCoefficient reals coefficients ->
    HasNonzeroCoefficient reals (coefficient ∷ coefficients)

Nonconstant :
  {R : Set} ->
  CompleteOrderedField R ->
  Polynomial R ->
  Set
Nonconstant reals [] =
  Bottom
Nonconstant reals (constant ∷ higher-coefficients) =
  HasNonzeroCoefficient reals higher-coefficients

AlgebraicallyClosedComplex :
  (R : Set) ->
  CompleteOrderedField R ->
  Set
AlgebraicallyClosedComplex R reals =
  (coefficients : Polynomial R) ->
  Nonconstant reals coefficients ->
  Exists (Complex R)
    (\ root ->
      evaluate reals coefficients root == zeroC reals)

fundamental-theorem-of-algebra : Set1
fundamental-theorem-of-algebra =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  AlgebraicallyClosedComplex R reals
