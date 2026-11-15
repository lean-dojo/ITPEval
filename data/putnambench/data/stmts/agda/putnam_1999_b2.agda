-- Statement-only formalization of PutnamBench corpus artifact putnam_1999_b2
-- (putnambench__agda__putnam_1999_b2): a complex polynomial satisfying
-- P(x) = Q(x)P''(x) for quadratic Q has degree-many distinct roots if it has
-- two distinct roots. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

twoN : Nat
twoN =
  suc (suc zero)

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
        (\ n -> lessOrEqual x (fromNat n))
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

complexOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexFromNat :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Complex R
complexFromNat reals n =
  complex (fromNat reals n) (zeroR reals)

complexPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Nat ->
  Complex R
complexPower reals z zero =
  complexOne reals
complexPower reals z (suc n) =
  complexMultiply reals (complexPower reals z n) z

sumFinComplex :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Complex R) ->
  Complex R
sumFinComplex reals {zero} terms =
  complexZero reals
sumFinComplex reals {suc n} terms =
  complexAdd reals
    (terms fzero)
    (sumFinComplex reals (\ i -> terms (fsuc i)))

record Polynomial
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set where
  field
    coefficient : Nat -> Complex R
    degree      : Nat

    higher-coefficients-zero :
      (k : Nat) ->
      degree <N k ->
      coefficient k == complexZero reals

    leading-or-zero :
      coefficient degree != complexZero reals
      or
      (((k : Nat) ->
        coefficient k == complexZero reals)
      and
      degree == zero)

open Polynomial

polynomialValue :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  Complex R ->
  Complex R
polynomialValue reals polynomial z =
  sumFinComplex reals
    {suc (degree polynomial)}
    (\ i ->
      complexMultiply reals
        (coefficient polynomial (finToNat i))
        (complexPower reals z (finToNat i)))

secondDerivativeValue :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  Complex R ->
  Complex R
secondDerivativeValue reals polynomial z =
  sumFinComplex reals
    {suc (degree polynomial)}
    (\ i ->
      let n = finToNat i
      in
      complexMultiply reals
        (complexFromNat reals
          ((suc n) * (suc (suc n))))
        (complexMultiply reals
          (coefficient polynomial (suc (suc n)))
          (complexPower reals z n)))

module Putnam1999B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Quadratic :
    Polynomial reals ->
    Set
  Quadratic Q =
    degree Q == twoN

  PolynomialEquation :
    Polynomial reals ->
    Polynomial reals ->
    Set
  PolynomialEquation P Q =
    (x : Complex R) ->
    polynomialValue reals P x ==
    complexMultiply reals
      (polynomialValue reals Q x)
      (secondDerivativeValue reals P x)

  IsRoot :
    Polynomial reals ->
    Complex R ->
    Set
  IsRoot P z =
    polynomialValue reals P z == complexZero reals

  HasTwoDistinctRoots :
    Polynomial reals ->
    Set
  HasTwoDistinctRoots P =
    Exists (Complex R)
      (\ x1 ->
        Exists (Complex R)
          (\ x2 ->
            x1 != x2
            and
            IsRoot P x1
            and
            IsRoot P x2))

  HasDegreeManyDistinctRoots :
    Polynomial reals ->
    Set
  HasDegreeManyDistinctRoots P =
    Exists (Fin (degree P) -> Complex R)
      (\ roots ->
        ((i j : Fin (degree P)) ->
          i != j ->
          roots i != roots j)
        and
        ((i : Fin (degree P)) ->
          IsRoot P (roots i)))

  proposition : Set
  proposition =
    (P Q : Polynomial reals) ->
    Quadratic Q ->
    PolynomialEquation P Q ->
    HasTwoDistinctRoots P ->
    HasDegreeManyDistinctRoots P

putnam-1999-b2 : Set1
putnam-1999-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1999B2Statement.proposition reals
