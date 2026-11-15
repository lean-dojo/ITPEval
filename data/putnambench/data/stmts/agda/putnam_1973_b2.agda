-- Statement-only formalization of PutnamBench corpus artifact putnam_1973_b2:
-- a complex number with rational coordinates and modulus one has rational
-- modulus after subtracting one from every even integer power; the equivalent
-- reciprocal-modulus formulation for natural powers is also included. This
-- file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

fromRational :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Rational ->
  R
fromRational reals q =
  divide reals
    (fromInt reals (numerator q))
    (fromNat reals (denominator q))

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

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

complexInverse :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexInverse reals z =
  let
    reciprocalSquaredModulus =
      inverse reals (complexSquaredModulus reals z)
  in
  complex
    (multiply reals
      (realPart z)
      reciprocalSquaredModulus)
    (negate reals
      (multiply reals
        (imaginaryPart z)
        reciprocalSquaredModulus))

complexNaturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Nat ->
  Complex R
complexNaturalPower reals z zero =
  complexOne reals
complexNaturalPower reals z (suc n) =
  complexMultiply reals
    (complexNaturalPower reals z n)
    z

complexIntegerPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Int ->
  Complex R
complexIntegerPower reals z (pos n) =
  complexNaturalPower reals z n
complexIntegerPower reals z (negsuc n) =
  complexNaturalPower reals
    (complexInverse reals z)
    (suc n)

doubleInt : Int -> Int
doubleInt (pos n) =
  pos (n + n)
doubleInt (negsuc n) =
  negsuc (suc (n + n))

twoN : Nat
twoN =
  suc (suc zero)

module Putnam1973B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  IsRational : R -> Set
  IsRational x =
    Exists Rational
      (\ q -> x == fromRational reals q)

  HasRationalCoordinates : Complex R -> Set
  HasRationalCoordinates z =
    Exists Rational
      (\ q1 ->
        Exists Rational
          (\ q2 ->
            realPart z == fromRational reals q1
            and
            imaginaryPart z == fromRational reals q2))

  evenIntegerPowerDistance : Complex R -> Int -> R
  evenIntegerPowerDistance z n =
    complexModulus reals
      (complexSubtract reals
        (complexIntegerPower reals z (doubleInt n))
        (complexOne reals))

  reciprocalEvenNaturalPowerDistance :
    Complex R ->
    Nat ->
    R
  reciprocalEvenNaturalPowerDistance z n =
    complexModulus reals
      (complexInverse reals
        (complexSubtract reals
          (complexNaturalPower reals z (twoN * n))
          (complexOne reals)))

  proposition : Set
  proposition =
    (z : Complex R) ->
    HasRationalCoordinates z ->
    complexModulus reals z == oneR reals ->
    ((n : Int) ->
      IsRational (evenIntegerPowerDistance z n))
    and
    ((n : Nat) ->
      IsRational
        (reciprocalEvenNaturalPowerDistance z n))

putnam-1973-b2 : Set1
putnam-1973-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1973B2Statement.proposition reals
