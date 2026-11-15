-- Statement-only formalization of PutnamBench corpus artifact putnam_1983_b6:
-- a nontrivial (2^n + 1)-st root of unity admits two
-- integer-coefficient polynomials whose values have squares summing to -1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  oneN
naturalPower base (suc exponent) =
  base * naturalPower base exponent

integerToReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
integerToReal reals (pos n) =
  fromNat reals n
integerToReal reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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

complexNegativeOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexNegativeOne reals =
  complex (negate reals (oneR reals)) (zeroR reals)

embedInteger :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  Complex R
embedInteger reals coefficient =
  complex (integerToReal reals coefficient) (zeroR reals)

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

complexSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexSquare reals z =
  complexMultiply reals z z

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

Polynomial : Set
Polynomial =
  List Int

polynomialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial ->
  Complex R ->
  Complex R
polynomialValue reals [] z =
  complexZero reals
polynomialValue reals (coefficient ∷ coefficients) z =
  complexAdd reals
    (embedInteger reals coefficient)
    (complexMultiply reals z
      (polynomialValue reals coefficients z))

module Putnam1983B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  rootExponent : Nat -> Nat
  rootExponent n =
    naturalPower twoN n + oneN

  IsNontrivialRoot : Nat -> Complex R -> Set
  IsNontrivialRoot n alpha =
    complexSubtract reals
      (complexPower reals alpha (rootExponent n))
      (complexOne reals)
    ==
    complexZero reals
    and
    alpha != complexOne reals

  HasPolynomialWitnesses : Complex R -> Set
  HasPolynomialWitnesses alpha =
    Exists Polynomial
      (\ p ->
        Exists Polynomial
          (\ q ->
            complexAdd reals
              (complexSquare reals (polynomialValue reals p alpha))
              (complexSquare reals (polynomialValue reals q alpha))
            ==
            complexNegativeOne reals))

  proposition : Set
  proposition =
    (n : Nat) ->
    zero <N n ->
    (alpha : Complex R) ->
    IsNontrivialRoot n alpha ->
    HasPolynomialWitnesses alpha

putnam-1983-b6 : Set1
putnam-1983-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1983B6Statement.proposition reals
