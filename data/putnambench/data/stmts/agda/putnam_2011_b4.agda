-- Statement-only formalization of PutnamBench corpus artifact putnam_2011_b4
-- (putnambench__agda__putnam_2011_b4): the determinant of the complex
-- tournament standings matrix is a nonnegative integer divisible by 2^2010.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2011B4 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

ifNat : Bool -> Nat -> Nat -> Nat
ifNat true whenTrue whenFalse =
  whenTrue
ifNat false whenTrue whenFalse =
  whenFalse

sameOutcome : Bool -> Bool -> Bool
sameOutcome true true =
  true
sameOutcome true false =
  false
sameOutcome false true =
  false
sameOutcome false false =
  true

wonAndLost : Bool -> Bool -> Bool
wonAndLost true false =
  true
wonAndLost true true =
  false
wonAndLost false true =
  false
wonAndLost false false =
  false

countTrue :
  {n : Nat} ->
  (Fin n -> Bool) ->
  Nat
countTrue {zero} predicate =
  zero
countTrue {suc n} predicate =
  ifNat
    (predicate fzero)
    (suc (countTrue (\ i -> predicate (fsuc i))))
    (countTrue (\ i -> predicate (fsuc i)))

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

imaginaryUnit :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
imaginaryUnit reals =
  complex (zeroR reals) (oneR reals)

complexFromNat :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Complex R
complexFromNat reals n =
  complex (fromNat reals n) (zeroR reals)

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

Matrix : Set -> Nat -> Set
Matrix A n =
  Fin n -> Fin n -> A

sumFinComplex :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Complex R) ->
  Complex R
sumFinComplex reals {zero} term =
  complexZero reals
sumFinComplex reals {suc n} term =
  complexAdd reals
    (term fzero)
    (sumFinComplex reals (\ i -> term (fsuc i)))

skip :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skip {zero} removed ()
skip {suc n} fzero i =
  fsuc i
skip {suc n} (fsuc removed) fzero =
  fzero
skip {suc n} (fsuc removed) (fsuc i) =
  fsuc (skip removed i)

firstRowMinor :
  {A : Set} {n : Nat} ->
  Matrix A (suc n) ->
  Fin (suc n) ->
  Matrix A n
firstRowMinor matrix removedColumn i j =
  matrix (fsuc i) (skip removedColumn j)

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Fin n ->
  Complex R
alternatingSign reals fzero =
  complexOne reals
alternatingSign reals (fsuc i) =
  complexNegate reals (alternatingSign reals i)

determinant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix (Complex R) n ->
  Complex R
determinant reals {zero} matrix =
  complexOne reals
determinant reals {suc n} matrix =
  sumFinComplex reals
    (\ column ->
      complexMultiply reals
        (alternatingSign reals column)
        (complexMultiply reals
          (matrix fzero column)
          (determinant reals (firstRowMinor matrix column))))

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  suc zero
naturalPower base (suc exponent) =
  base * naturalPower base exponent

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Exists Nat
    (\ quotient -> divisor * quotient == dividend)

playerCount : Nat
playerCount =
  2011

gameCount : Nat
gameCount =
  2011

Games : Set
Games =
  Fin gameCount -> Fin playerCount -> Bool

expectedT :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Games ->
  Matrix (Complex R) playerCount
expectedT reals games player1 player2 =
  complexFromNat reals
    (countTrue
      (\ game ->
        sameOutcome
          (games game player1)
          (games game player2)))

expectedW :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Games ->
  Matrix (Complex R) playerCount
expectedW reals games player1 player2 =
  complexSubtract reals
    (complexFromNat reals
      (countTrue
        (\ game ->
          wonAndLost
            (games game player1)
            (games game player2))))
    (complexFromNat reals
      (countTrue
        (\ game ->
          wonAndLost
            (games game player2)
            (games game player1))))

tournamentMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix (Complex R) playerCount ->
  Matrix (Complex R) playerCount ->
  Matrix (Complex R) playerCount
tournamentMatrix reals T W player1 player2 =
  complexAdd reals
    (T player1 player2)
    (complexMultiply reals
      (imaginaryUnit reals)
      (W player1 player2))

putnam-2011-b4 : Set1
putnam-2011-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (games : Games) ->
  (T W : Matrix (Complex R) playerCount) ->
  T == expectedT reals games ->
  W == expectedW reals games ->
  Exists Nat
    (\ n ->
      determinant reals (tournamentMatrix reals T W) ==
      complexFromNat reals n
      and
      Divides (naturalPower 2 2010) n)
