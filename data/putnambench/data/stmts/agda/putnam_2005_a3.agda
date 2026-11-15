-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_a3:
-- every nonzero critical point of a positive-degree complex polynomial divided
-- by the corresponding half-natural power lies on the unit circle when all
-- polynomial zeros lie there. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005A3 where

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
    addR multiplyR : R -> R -> R
    negateR inverseR squareRootR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverseR-zero :
      inverseR zeroR == zeroR
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNatR-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNatR-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
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

    square-rootR-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR (squareRootR x)
    square-rootR-square :
      (x : R) ->
      lessOrEqualR zeroR x ->
      multiplyR (squareRootR x) (squareRootR x) == x
    square-rootR-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      squareRootR x == zeroR
    square-rootR-unique :
      (x y : R) ->
      lessOrEqualR zeroR y ->
      multiplyR y y == x ->
      y == squareRootR x

open CompleteOrderedRealField

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

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

complexAdd :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals z w =
  complex
    (addR reals (realPart z) (realPart w))
    (addR reals (imaginaryPart z) (imaginaryPart w))

complexNegate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexNegate reals z =
  complex
    (negateR reals (realPart z))
    (negateR reals (imaginaryPart z))

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
    (addR reals
      (multiplyR reals (realPart z) (realPart w))
      (negateR reals
        (multiplyR reals (imaginaryPart z) (imaginaryPart w))))
    (addR reals
      (multiplyR reals (realPart z) (imaginaryPart w))
      (multiplyR reals (imaginaryPart z) (realPart w)))

complexSquaredModulus :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexSquaredModulus reals z =
  addR reals
    (multiplyR reals (realPart z) (realPart z))
    (multiplyR reals (imaginaryPart z) (imaginaryPart z))

complexModulus :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexModulus reals z =
  squareRootR reals (complexSquaredModulus reals z)

complexInverse :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexInverse reals z =
  let denominator = complexSquaredModulus reals z
  in
  complex
    (multiplyR reals
      (realPart z)
      (inverseR reals denominator))
    (negateR reals
      (multiplyR reals
        (imaginaryPart z)
        (inverseR reals denominator)))

complexDivide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexDivide reals z w =
  complexMultiply reals z (complexInverse reals w)

complexNaturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Nat ->
  Complex R
complexNaturalPower reals z zero =
  complexOne reals
complexNaturalPower reals z (suc n) =
  complexMultiply reals (complexNaturalPower reals z n) z

record StandardComplexSquareRoot
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where

  field
    squareRootC : Complex R -> Complex R
    squareRootC-square :
      (z : Complex R) ->
      complexMultiply reals (squareRootC z) (squareRootC z) == z
    squareRootC-real-nonnegative :
      (z : Complex R) ->
      lessOrEqualR reals
        (zeroR reals)
        (realPart (squareRootC z))
    squareRootC-imaginary-nonnegative-when-real-zero :
      (z : Complex R) ->
      realPart (squareRootC z) == zeroR reals ->
      lessOrEqualR reals
        (zeroR reals)
        (imaginaryPart (squareRootC z))

open StandardComplexSquareRoot

complexHalfNaturalPower :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardComplexSquareRoot reals ->
  Complex R ->
  Nat ->
  Complex R
complexHalfNaturalPower reals roots z zero =
  complexOne reals
complexHalfNaturalPower reals roots z (suc zero) =
  squareRootC roots z
complexHalfNaturalPower reals roots z (suc (suc n)) =
  complexMultiply reals z
    (complexHalfNaturalPower reals roots z n)

sumInclusive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> Complex R) ->
  Complex R
sumInclusive reals zero term =
  term zero
sumInclusive reals (suc n) term =
  complexAdd reals
    (sumInclusive reals n term)
    (term (suc n))

record PolynomialOfDegree
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (degree : Nat) : Set where

  field
    coefficient : Nat -> Complex R
    coefficients-above-degree :
      (k : Nat) ->
      degree <N k ->
      coefficient k == complexZero reals
    leading-coefficient-nonzero :
      coefficient degree != complexZero reals

open PolynomialOfDegree

evaluate :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {degree : Nat} ->
  PolynomialOfDegree reals degree ->
  Complex R ->
  Complex R
evaluate reals {degree} polynomial z =
  sumInclusive reals degree
    (\ k ->
      complexMultiply reals
        (coefficient polynomial k)
        (complexNaturalPower reals z k))

ComplexDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Complex R -> Complex R) ->
  Complex R ->
  Complex R ->
  Set
ComplexDerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((z : Complex R) ->
        StrictLess reals
          (complexModulus reals
            (complexSubtract reals z point))
          delta ->
        z != point ->
        StrictLess reals
          (complexModulus reals
            (complexSubtract reals
              (complexDivide reals
                (complexSubtract reals
                  (function z)
                  (function point))
                (complexSubtract reals z point))
              derivativeValue))
          epsilon))

module Putnam2005A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (roots : StandardComplexSquareRoot reals)
  (n : Nat)
  (polynomial : PolynomialOfDegree reals n)
  (g : Complex R -> Complex R) where

  GDefinition : Set
  GDefinition =
    (z : Complex R) ->
    g z ==
    complexDivide reals
      (evaluate reals polynomial z)
      (complexHalfNaturalPower reals roots z n)

  AllPolynomialZerosOnUnitCircle : Set
  AllPolynomialZerosOnUnitCircle =
    (z : Complex R) ->
    evaluate reals polynomial z == complexZero reals ->
    complexModulus reals z == oneR reals

  proposition : Set
  proposition =
    zero <N n ->
    AllPolynomialZerosOnUnitCircle ->
    GDefinition ->
    (z : Complex R) ->
    z != complexZero reals ->
    ComplexDerivativeAt reals g z (complexZero reals) ->
    complexModulus reals z == oneR reals

putnam-2005-a3 : Set1
putnam-2005-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (roots : StandardComplexSquareRoot reals) ->
  (n : Nat) ->
  (polynomial : PolynomialOfDegree reals n) ->
  (g : Complex R -> Complex R) ->
  Putnam2005A3Statement.proposition
    reals
    roots
    n
    polynomial
    g
