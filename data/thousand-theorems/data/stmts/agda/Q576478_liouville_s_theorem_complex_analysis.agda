-- Statement-only formalization of thousand-theorems corpus artifact Q576478,
-- "Liouville's theorem (complex analysis)": an everywhere complex
-- Frechet-differentiable map between complex normed vector spaces whose range
-- is bounded takes equal values at every two points. This file contains no proof.

{-# OPTIONS --safe #-}

module Q576478_liouville_s_theorem_complex_analysis where

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

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals (complex a b) (complex c d) =
  complex
    (addR reals a c)
    (addR reals b d)

complexNegate :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R
complexNegate reals (complex a b) =
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

complexMultiply :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals (complex a b) (complex c d) =
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
      normC (complexZero reals) == zeroR reals
    norm-zero-onlyC :
      (z : Complex R) ->
      normC z == zeroR reals ->
      z == complexZero reals
    norm-negateC :
      (z : Complex R) ->
      normC (complexNegate reals z) == normC z
    norm-addC :
      (z w : Complex R) ->
      lessOrEqualR reals
        (normC (complexAdd reals z w))
        (addR reals (normC z) (normC w))
    norm-multiplyC :
      (z w : Complex R) ->
      normC (complexMultiply reals z w) ==
      multiplyR reals (normC z) (normC w)
    norm-squareC :
      (z : Complex R) ->
      multiplyR reals (normC z) (normC z) ==
      addR reals
        (multiplyR reals (realPart z) (realPart z))
        (multiplyR reals (imaginaryPart z) (imaginaryPart z))

open ComplexNorm

record NormedComplexVectorSpace
  {R : Set}
  (reals : CompleteOrderedField R)
  (complexNorm : ComplexNorm reals)
  (E : Set) : Set1 where
  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : Complex R -> E -> E
    normE : E -> R

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    scale-oneE :
      (x : E) ->
      scaleE (complexOne reals) x == x
    scale-associativeE :
      (a b : Complex R) ->
      (x : E) ->
      scaleE (complexMultiply reals a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectorsE :
      (a : Complex R) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalarsE :
      (a b : Complex R) ->
      (x : E) ->
      scaleE (complexAdd reals a b) x ==
      addE (scaleE a x) (scaleE b x)

    norm-nonnegativeE :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normE x)
    norm-zeroE :
      normE zeroE == zeroR reals
    norm-zero-onlyE :
      (x : E) ->
      normE x == zeroR reals ->
      x == zeroE
    norm-negateE :
      (x : E) ->
      normE (negateE x) == normE x
    norm-addE :
      (x y : E) ->
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scaleE :
      (a : Complex R) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR reals (normC complexNorm a) (normE x)

open NormedComplexVectorSpace

subtractE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

ComplexLinear :
  {R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  (source : NormedComplexVectorSpace reals complexNorm E) ->
  (target : NormedComplexVectorSpace reals complexNorm F) ->
  (E -> F) ->
  Set
ComplexLinear {R = R} source target linear =
  Both
    ((x y : _) ->
      linear (addE source x y) ==
      addE target (linear x) (linear y))
    ((scalar : Complex R) ->
      (x : _) ->
      linear (scaleE source scalar x) ==
      scaleE target scalar (linear x))

BoundedOperator :
  {R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  (source : NormedComplexVectorSpace reals complexNorm E) ->
  (target : NormedComplexVectorSpace reals complexNorm F) ->
  (E -> F) ->
  Set
BoundedOperator {R = R} {reals = reals} source target linear =
  Exists R
    (\ bound ->
      Both
        (lessOrEqualR reals (zeroR reals) bound)
        ((x : _) ->
          lessOrEqualR reals
            (normE target (linear x))
            (multiplyR reals bound (normE source x))))

FrechetApproximationAt :
  {R E F : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  (source : NormedComplexVectorSpace reals complexNorm E) ->
  (target : NormedComplexVectorSpace reals complexNorm F) ->
  (E -> F) ->
  (E -> F) ->
  E ->
  Set
FrechetApproximationAt reals source target function linear point =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists _
    (\ delta ->
      Both
        (Positive reals delta)
        ((increment : _) ->
          StrictLess reals (normE source increment) delta ->
          lessOrEqualR reals
            (normE target
              (subtractE target
                (subtractE target
                  (function (addE source point increment))
                  (function point))
                (linear increment)))
            (multiplyR reals epsilon (normE source increment))))

FrechetDifferentiableAt :
  {R E F : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  (source : NormedComplexVectorSpace reals complexNorm E) ->
  (target : NormedComplexVectorSpace reals complexNorm F) ->
  (E -> F) ->
  E ->
  Set
FrechetDifferentiableAt reals source target function point =
  Exists (_ -> _)
    (\ linear ->
      Both
        (ComplexLinear source target linear)
        (Both
          (BoundedOperator source target linear)
          (FrechetApproximationAt
            reals source target function linear point)))

EverywhereComplexFrechetDifferentiable :
  {R E F : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  (source : NormedComplexVectorSpace reals complexNorm E) ->
  (target : NormedComplexVectorSpace reals complexNorm F) ->
  (E -> F) ->
  Set
EverywhereComplexFrechetDifferentiable reals source target function =
  (point : _) ->
  FrechetDifferentiableAt reals source target function point

BoundedRange :
  {R E F : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm F ->
  (E -> F) ->
  Set
BoundedRange {R = R} reals target function =
  Exists R
    (\ bound ->
      (x : _) ->
      lessOrEqualR reals (normE target (function x)) bound)

liouville-s-theorem-complex-analysis : Set1
liouville-s-theorem-complex-analysis =
  (R E F : Set) ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (source : NormedComplexVectorSpace reals complexNorm E) ->
  (target : NormedComplexVectorSpace reals complexNorm F) ->
  (function : E -> F) ->
  EverywhereComplexFrechetDifferentiable
    reals source target function ->
  BoundedRange reals target function ->
  (z w : E) ->
  function z == function w
