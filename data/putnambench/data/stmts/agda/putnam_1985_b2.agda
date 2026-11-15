-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_b2:
-- a polynomial sequence defined by its initial value, zero constant terms,
-- and a derivative-shift recurrence has f_100(1) = 101^99, with 101 prime.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _divides_
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

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record Prime (n : Nat) : Set where
  field
    at-least-two :
      2 <=N n
    divisor-is-trivial :
      (d : Nat) ->
      d divides n ->
      d == 1 or d == n

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

oneN : Nat
oneN =
  suc zero

powerNat : Nat -> Nat -> Nat
powerNat base zero =
  oneN
powerNat base (suc exponent) =
  base * powerNat base exponent

Polynomial : Set -> Set
Polynomial R =
  List R

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluatePolynomial reals [] x =
  zeroR reals
evaluatePolynomial reals (coefficient ∷ coefficients) x =
  add reals
    coefficient
    (multiply reals x
      (evaluatePolynomial reals coefficients x))

PolynomialEqual :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Set
PolynomialEqual {R} reals p q =
  (x : R) ->
  evaluatePolynomial reals p x ==
  evaluatePolynomial reals q x

derivativeFrom :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Polynomial R ->
  Polynomial R
derivativeFrom reals degree [] =
  []
derivativeFrom reals degree (coefficient ∷ coefficients) =
  multiply reals
    (fromNat reals degree)
    coefficient
  ∷
  derivativeFrom reals (suc degree) coefficients

derivativePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R
derivativePolynomial reals [] =
  []
derivativePolynomial reals (constant ∷ coefficients) =
  derivativeFrom reals oneN coefficients

module Putnam1985B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  InitialValue :
    (Nat -> Polynomial R) ->
    Set
  InitialValue f =
    PolynomialEqual reals
      (f zero)
      (oneR reals ∷ [])

  ZeroConstantTerms :
    (Nat -> Polynomial R) ->
    Set
  ZeroConstantTerms f =
    (n : Nat) ->
    oneN <=N n ->
    evaluatePolynomial reals (f n) (zeroR reals) ==
    zeroR reals

  DerivativeRecurrence :
    (Nat -> Polynomial R) ->
    Set
  DerivativeRecurrence f =
    (n : Nat) ->
    (x : R) ->
    evaluatePolynomial reals
      (derivativePolynomial reals (f (suc n)))
      x
    ==
    multiply reals
      (fromNat reals (suc n))
      (evaluatePolynomial reals
        (f n)
        (add reals x (oneR reals)))

  proposition : Set
  proposition =
    (f : Nat -> Polynomial R) ->
    InitialValue f ->
    ZeroConstantTerms f ->
    DerivativeRecurrence f ->
    Prime 101
    and
    (evaluatePolynomial reals
      (f 100)
      (oneR reals)
    ==
    fromNat reals (powerNat 101 99))

putnam-1985-b2 : Set1
putnam-1985-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1985B2Statement.proposition reals
