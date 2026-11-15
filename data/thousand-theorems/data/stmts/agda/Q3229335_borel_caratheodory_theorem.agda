-- Statement-only formalization of thousand-theorems corpus artifact Q3229335,
-- "Borel–Carathéodory theorem": a holomorphic complex function on a ball whose
-- real part is bounded above satisfies the canonical interior norm estimate.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q3229335_borel_caratheodory_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
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
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

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
      Either (lessOrEqualR x y) (lessOrEqualR y x)
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
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqualR x (fromNatR n))
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
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (reciprocalR reals y)

twoR :
  {R : Set} ->
  CompleteOrderedField R ->
  R
twoR reals =
  fromNatR reals (suc (suc zero))

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

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

subtractC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
subtractC reals z w =
  addC reals z (negateC reals w)

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

record ComplexNorm
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    normC : Complex R -> R
    norm-nonnegativeC :
      (z : Complex R) ->
      lessOrEqualR reals (zeroR reals) (normC z)
    norm-zeroC :
      normC (zeroC reals) == zeroR reals
    norm-zero-onlyC :
      (z : Complex R) ->
      normC z == zeroR reals ->
      z == zeroC reals
    norm-negateC :
      (z : Complex R) ->
      normC (negateC reals z) == normC z
    norm-addC :
      (z w : Complex R) ->
      lessOrEqualR reals
        (normC (addC reals z w))
        (addR reals (normC z) (normC w))
    norm-multiplyC :
      (z w : Complex R) ->
      normC (multiplyC reals z w) ==
      multiplyR reals (normC z) (normC w)
    norm-squareC :
      (z : Complex R) ->
      multiplyR reals (normC z) (normC z) ==
      addR reals
        (multiplyR reals (realPart z) (realPart z))
        (multiplyR reals (imaginaryPart z) (imaginaryPart z))

open ComplexNorm

SetOf : Set -> Set1
SetOf A =
  A -> Set

OpenBallAtZero :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ComplexNorm reals ->
  R ->
  SetOf (Complex R)
OpenBallAtZero reals complexNorm radius z =
  StrictLess reals (normC complexNorm z) radius

DerivativeRemainder :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Complex R -> Complex R) ->
  Complex R ->
  Complex R ->
  Complex R ->
  Complex R
DerivativeRemainder reals f derivative point y =
  subtractC reals
    (subtractC reals (f y) (f point))
    (multiplyC reals
      (subtractC reals y point)
      derivative)

HasComplexDerivativeWithinAt :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (Complex R -> Complex R) ->
  SetOf (Complex R) ->
  Complex R ->
  Complex R ->
  Set
HasComplexDerivativeWithinAt {R = R}
  reals complexNorm f U point derivative =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((y : Complex R) ->
          U y ->
          StrictLess reals
            (normC complexNorm (subtractC reals y point))
            delta ->
          lessOrEqualR reals
            (normC complexNorm
              (DerivativeRemainder
                reals f derivative point y))
            (multiplyR reals epsilon
              (normC complexNorm
                (subtractC reals y point)))))

DifferentiableWithinAt :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (Complex R -> Complex R) ->
  SetOf (Complex R) ->
  Complex R ->
  Set
DifferentiableWithinAt
  reals complexNorm f U point =
  Exists (Complex _)
    (HasComplexDerivativeWithinAt
      reals complexNorm f U point)

DifferentiableOn :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (Complex R -> Complex R) ->
  SetOf (Complex R) ->
  Set
DifferentiableOn {R = R}
  reals complexNorm f U =
  (point : Complex R) ->
  U point ->
  DifferentiableWithinAt
    reals complexNorm f U point

MapsRealPartAtMost :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Complex R -> Complex R) ->
  SetOf (Complex R) ->
  R ->
  Set
MapsRealPartAtMost {R = R} reals f U bound =
  (point : Complex R) ->
  U point ->
  lessOrEqualR reals (realPart (f point)) bound

BorelCaratheodoryBound :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ComplexNorm reals ->
  R ->
  R ->
  (Complex R -> Complex R) ->
  Complex R ->
  R
BorelCaratheodoryBound reals complexNorm bound radius f z =
  addR reals
    (divideR reals
      (multiplyR reals
        (multiplyR reals (twoR reals) bound)
        (normC complexNorm z))
      (subtractR reals radius (normC complexNorm z)))
    (divideR reals
      (multiplyR reals
        (normC complexNorm (f (zeroC reals)))
        (addR reals radius (normC complexNorm z)))
      (subtractR reals radius (normC complexNorm z)))

borel-caratheodory-theorem : Set1
borel-caratheodory-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (f : Complex R -> Complex R) ->
  (bound radius : R) ->
  (z : Complex R) ->
  Positive reals bound ->
  DifferentiableOn reals complexNorm f
    (OpenBallAtZero reals complexNorm radius) ->
  MapsRealPartAtMost reals f
    (OpenBallAtZero reals complexNorm radius)
    bound ->
  Positive reals radius ->
  OpenBallAtZero reals complexNorm radius z ->
  lessOrEqualR reals
    (normC complexNorm (f z))
    (BorelCaratheodoryBound
      reals complexNorm bound radius f z)
