-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_a3
-- (putnambench__agda__putnam_2019_a3): the greatest universal lower bound
-- for the average modulus of the roots of a degree-2019 polynomial with
-- strictly increasing real coefficients from 1 to 2019. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data HasLength {A : Set} : List A -> Nat -> Set where
  length-empty :
    HasLength [] zero
  length-cons :
    {x : A} {xs : List A} {n : Nat} ->
    HasLength xs n ->
    HasLength (x ∷ xs) (suc n)

data LastElement {A : Set} : List A -> A -> Set where
  last-singleton :
    {x : A} ->
    LastElement (x ∷ []) x
  last-cons :
    {x last : A} {xs : List A} ->
    LastElement xs last ->
    LastElement (x ∷ xs) last

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

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

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
  multiply reals x (naturalPower reals x n)

data StrictlyIncreasing
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  List R -> Set where

  increasing-empty :
    StrictlyIncreasing reals []
  increasing-singleton :
    {x : R} ->
    StrictlyIncreasing reals (x ∷ [])
  increasing-cons :
    {x y : R} {xs : List R} ->
    StrictLess reals x y ->
    StrictlyIncreasing reals (y ∷ xs) ->
    StrictlyIncreasing reals (x ∷ y ∷ xs)

data FirstAtLeastOne
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  List R -> Set where

  first-at-least-one :
    {x : R} {xs : List R} ->
    lessOrEqual reals (oneR reals) x ->
    FirstAtLeastOne reals (x ∷ xs)

data LastAtMost2019
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  List R -> Set where

  last-at-most :
    {x : R} ->
    lessOrEqual reals x (fromNat reals 2019) ->
    LastAtMost2019 reals (x ∷ [])
  preceding-coefficient :
    {x : R} {xs : List R} ->
    LastAtMost2019 reals xs ->
    LastAtMost2019 reals (x ∷ xs)

CoefficientConditions :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List R ->
  Set
CoefficientConditions reals coefficients =
  HasLength coefficients 2020
  and
  FirstAtLeastOne reals coefficients
  and
  LastAtMost2019 reals coefficients
  and
  StrictlyIncreasing reals coefficients

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

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

realComplex :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Complex R
realComplex reals x =
  complex x (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals (complex a b) (complex c d) =
  complex
    (add reals a c)
    (add reals b d)

complexNegate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexNegate reals (complex a b) =
  complex
    (negate reals a)
    (negate reals b)

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
complexMultiply reals (complex a b) (complex c d) =
  complex
    (add reals
      (multiply reals a c)
      (negate reals (multiply reals b d)))
    (add reals
      (multiply reals a d)
      (multiply reals b c))

complexScale :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Complex R ->
  Complex R
complexScale reals scalar (complex a b) =
  complex
    (multiply reals scalar a)
    (multiply reals scalar b)

squaredMagnitude :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
squaredMagnitude reals (complex a b) =
  add reals
    (multiply reals a a)
    (multiply reals b b)

complexMagnitude :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexMagnitude reals z =
  squareRoot reals (squaredMagnitude reals z)

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List R ->
  Complex R ->
  Complex R
evaluatePolynomial reals [] z =
  complexZero reals
evaluatePolynomial reals (coefficient ∷ coefficients) z =
  complexAdd reals
    (realComplex reals coefficient)
    (complexMultiply reals z
      (evaluatePolynomial reals coefficients z))

rootFactorProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List (Complex R) ->
  Complex R ->
  Complex R
rootFactorProduct reals [] z =
  complexOne reals
rootFactorProduct reals (root ∷ roots) z =
  complexMultiply reals
    (complexSubtract reals z root)
    (rootFactorProduct reals roots z)

RootEnumeration :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List R ->
  List (Complex R) ->
  Set
RootEnumeration {R} reals coefficients roots =
  HasLength roots 2019
  and
  Exists R
    (\ leadingCoefficient ->
      LastElement coefficients leadingCoefficient
      and
      ((z : Complex R) ->
        evaluatePolynomial reals coefficients z ==
        complexScale reals leadingCoefficient
          (rootFactorProduct reals roots z)))

sumRootMagnitudes :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List (Complex R) ->
  R
sumRootMagnitudes reals [] =
  zeroR reals
sumRootMagnitudes reals (root ∷ roots) =
  add reals
    (complexMagnitude reals root)
    (sumRootMagnitudes reals roots)

averageRootMagnitude :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List (Complex R) ->
  R
averageRootMagnitude reals roots =
  divide reals
    (sumRootMagnitudes reals roots)
    (fromNat reals 2019)

PutnamSolutionValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
PutnamSolutionValue reals solution =
  StrictLess reals (zeroR reals) solution
  and
  multiply reals
    (naturalPower reals solution 2019)
    (fromNat reals 2019)
  ==
  oneR reals

UniversalLowerBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
UniversalLowerBound {R} reals lowerBound =
  (coefficients : List R) ->
  (roots : List (Complex R)) ->
  CoefficientConditions reals coefficients ->
  RootEnumeration reals coefficients roots ->
  lessOrEqual reals
    lowerBound
    (averageRootMagnitude reals roots)

record IsGreatestUniversalLowerBound
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (candidate : R) :
  Set where

  field
    candidate-is-lower-bound :
      UniversalLowerBound reals candidate

    greatest-among-lower-bounds :
      (other : R) ->
      UniversalLowerBound reals other ->
      lessOrEqual reals other candidate

putnam-2019-a3 : Set1
putnam-2019-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Exists R
    (\ solution ->
      PutnamSolutionValue reals solution
      and
      IsGreatestUniversalLowerBound reals solution)
