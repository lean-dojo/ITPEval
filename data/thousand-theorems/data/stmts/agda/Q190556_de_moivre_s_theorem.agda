-- Statement-only formalization of Thousand Theorems corpus artifact Q190556
-- (thousand-theorems__agda__Q190556), "De Moivre's theorem": natural powers
-- of cos z + i sin z equal cos (n z) + i sin (n z) for every complex z.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q190556_de_moivre_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR absoluteValueR : R -> R
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

    absolute-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR (absoluteValueR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteValueR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteValueR x == negateR x

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
        (\ n -> lessOrEqualR x (fromNatR n))
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

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

StrictLessR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLessR reals x y =
  lessOrEqualR reals x y and x != y

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

oneC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
oneC reals =
  complex (oneR reals) (zeroR reals)

imaginaryUnit :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
imaginaryUnit reals =
  complex (zeroR reals) (oneR reals)

fromNatC :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  Complex R
fromNatC reals n =
  complex (fromNatR reals n) (zeroR reals)

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
subtractC reals x y =
  addC reals x (negateC reals y)

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

scaleC :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Complex R ->
  Complex R
scaleC reals scalar (complex a b) =
  complex
    (multiplyR reals scalar a)
    (multiplyR reals scalar b)

powerC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Nat ->
  Complex R
powerC reals z zero =
  oneC reals
powerC reals z (suc n) =
  multiplyC reals (powerC reals z n) z

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Nat ->
  Complex R
exponentialTerm reals z n =
  scaleC reals
    (inverseR reals (fromNatR reals (factorial n)))
    (powerC reals z n)

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Nat ->
  Complex R
exponentialPartialSum reals z zero =
  zeroC reals
exponentialPartialSum reals z (suc n) =
  addC reals
    (exponentialPartialSum reals z n)
    (exponentialTerm reals z n)

ConvergesC :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> Complex R) ->
  Complex R ->
  Set
ConvergesC {R} reals sequence limit =
  (epsilon : R) ->
  StrictLessR reals (zeroR reals) epsilon ->
  Exists Nat
    (\ threshold ->
      (n : Nat) ->
      threshold <=N n ->
      (StrictLessR reals
        (absoluteValueR reals
          (subtractR reals
            (realPart (sequence n))
            (realPart limit)))
        epsilon)
      and
      (StrictLessR reals
        (absoluteValueR reals
          (subtractR reals
            (imaginaryPart (sequence n))
            (imaginaryPart limit)))
        epsilon))

record StandardComplexExponential
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where
  field
    exponential : Complex R -> Complex R
    exponential-is-power-series :
      (z : Complex R) ->
      ConvergesC reals
        (exponentialPartialSum reals z)
        (exponential z)

open StandardComplexExponential

twoN : Nat
twoN =
  suc (suc zero)

halfR :
  {R : Set} ->
  CompleteOrderedField R ->
  R
halfR reals =
  inverseR reals (fromNatR reals twoN)

cosineC :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardComplexExponential reals ->
  Complex R ->
  Complex R
cosineC reals standardExponential z =
  scaleC reals
    (halfR reals)
    (addC reals
      (exponential standardExponential
        (multiplyC reals z (imaginaryUnit reals)))
      (exponential standardExponential
        (multiplyC reals
          (negateC reals z)
          (imaginaryUnit reals))))

sineC :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardComplexExponential reals ->
  Complex R ->
  Complex R
sineC reals standardExponential z =
  scaleC reals
    (halfR reals)
    (multiplyC reals
      (subtractC reals
        (exponential standardExponential
          (multiplyC reals
            (negateC reals z)
            (imaginaryUnit reals)))
        (exponential standardExponential
          (multiplyC reals z (imaginaryUnit reals))))
      (imaginaryUnit reals))

de-moivre-s-theorem : Set1
de-moivre-s-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (standardExponential : StandardComplexExponential reals) ->
  (n : Nat) ->
  (z : Complex R) ->
  powerC reals
    (addC reals
      (cosineC reals standardExponential z)
      (multiplyC reals
        (sineC reals standardExponential z)
        (imaginaryUnit reals)))
    n
  ==
  addC reals
    (cosineC reals standardExponential
      (multiplyC reals (fromNatC reals n) z))
    (multiplyC reals
      (sineC reals standardExponential
        (multiplyC reals (fromNatC reals n) z))
      (imaginaryUnit reals))
