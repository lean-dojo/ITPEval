-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_b4
-- (putnambench__agda__putnam_2007_b4): counting ordered pairs of real
-- polynomials P and Q with P^2 + Q^2 = X^(2n) + 1 and deg P > deg Q.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

record Polynomial
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set where

  field
    coefficient :
      Nat ->
      R
    degree-bound :
      Nat
    coefficient-above-bound :
      (k : Nat) ->
      degree-bound <N k ->
      coefficient k == zeroR reals

open Polynomial

PolynomialEqual :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  Polynomial reals ->
  Polynomial reals ->
  Set
PolynomialEqual p q =
  (k : Nat) ->
  coefficient p k == coefficient q k

ZeroPolynomial :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  Set
ZeroPolynomial reals p =
  (k : Nat) ->
  coefficient p k == zeroR reals

LeadingDegree :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  Nat ->
  Set
LeadingDegree reals p d =
  coefficient p d != zeroR reals
  and
  ((k : Nat) ->
    d <N k ->
    coefficient p k == zeroR reals)

DegreeGreater :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  Polynomial reals ->
  Set
DegreeGreater reals p q =
  Exists Nat
    (\ p-degree ->
      LeadingDegree reals p p-degree
      and
      (ZeroPolynomial reals q
      or
      Exists Nat
        (\ q-degree ->
          LeadingDegree reals q q-degree
          and
          q-degree <N p-degree)))

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

productCoefficient :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  Polynomial reals ->
  Nat ->
  R
productCoefficient reals p q k =
  sumFirst reals (suc k)
    (\ i ->
      multiply reals
        (coefficient p i)
        (coefficient q (k - i)))

squareSumCoefficient :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  Polynomial reals ->
  Nat ->
  R
squareSumCoefficient reals p q k =
  add reals
    (productCoefficient reals p p k)
    (productCoefficient reals q q k)

record PolynomialEquation
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (n : Nat)
  (p q : Polynomial reals) :
  Set where

  field
    constant-coefficient :
      squareSumCoefficient reals p q zero ==
      oneR reals
    leading-coefficient :
      squareSumCoefficient reals p q (n + n) ==
      oneR reals
    all-other-coefficients :
      (k : Nat) ->
      k != zero ->
      k != n + n ->
      squareSumCoefficient reals p q k ==
      zeroR reals

record PolynomialPair
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set where

  constructor pair
  field
    first-polynomial  : Polynomial reals
    second-polynomial : Polynomial reals

open PolynomialPair

PairEqual :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  PolynomialPair reals ->
  PolynomialPair reals ->
  Set
PairEqual left-pair right-pair =
  PolynomialEqual
    (first-polynomial left-pair)
    (first-polynomial right-pair)
  and
  PolynomialEqual
    (second-polynomial left-pair)
    (second-polynomial right-pair)

QualifyingPair :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Nat ->
  PolynomialPair reals ->
  Set
QualifyingPair reals n polynomial-pair =
  PolynomialEquation reals n
    (first-polynomial polynomial-pair)
    (second-polynomial polynomial-pair)
  and
  DegreeGreater reals
    (first-polynomial polynomial-pair)
    (second-polynomial polynomial-pair)

record HasExtensionalCardinality
  {A : Set}
  (P : A -> Set)
  (equivalent : A -> A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (item : A) ->
      P item ->
      Exists (Fin cardinality)
        (\ index ->
          equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

twoN : Nat
twoN =
  suc (suc zero)

naturalPowerNat : Nat -> Nat -> Nat
naturalPowerNat base zero =
  suc zero
naturalPowerNat base (suc exponent) =
  base * naturalPowerNat base exponent

putnam-2007-b4 : Set1
putnam-2007-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  zero <N n ->
  HasExtensionalCardinality
    (QualifyingPair reals n)
    PairEqual
    (naturalPowerNat twoN (suc n))
