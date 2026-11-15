-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_a4
-- (putnambench__agda__putnam_2025_a4): the least dimension of 2025 real
-- square matrices with exactly the prescribed commuting pairs is three.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2025A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_
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

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value     : A
    satisfies : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

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
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      (x : R) ->
      lessOrEqual x x
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

Matrix : Set -> Nat -> Set
Matrix R dimension =
  Fin dimension -> Fin dimension -> R

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

matrixMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {dimension : Nat} ->
  Matrix R dimension ->
  Matrix R dimension ->
  Matrix R dimension
matrixMultiply reals leftMatrix rightMatrix row column =
  sumFin reals
    (\ middle ->
      multiply reals
        (leftMatrix row middle)
        (rightMatrix middle column))

MatrixEqual :
  {R : Set} ->
  {dimension : Nat} ->
  Matrix R dimension ->
  Matrix R dimension ->
  Set
MatrixEqual {dimension = dimension} leftMatrix rightMatrix =
  (row column : Fin dimension) ->
  leftMatrix row column == rightMatrix row column

Commute :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {dimension : Nat} ->
  Matrix R dimension ->
  Matrix R dimension ->
  Set
Commute reals leftMatrix rightMatrix =
  MatrixEqual
    (matrixMultiply reals leftMatrix rightMatrix)
    (matrixMultiply reals rightMatrix leftMatrix)

matrixCount : Nat
matrixCount =
  2025

AllowedGap : Nat -> Set
AllowedGap gap =
  (gap == 0) or (gap == 1) or (gap == 2024)

HasCommutationPattern :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Set
HasCommutationPattern {R} reals dimension =
  Exists (Fin matrixCount -> Matrix R dimension)
    (\ matrices ->
      (i j : Fin matrixCount) ->
      finToNat i <=N finToNat j ->
      Iff
        (Commute reals (matrices i) (matrices j))
        (AllowedGap (finToNat j - finToNat i)))

record IsLeastDimension
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (least : Nat) :
  Set where

  field
    attainable :
      HasCommutationPattern reals least
    lower-bound :
      (dimension : Nat) ->
      HasCommutationPattern reals dimension ->
      least <=N dimension

three : Nat
three =
  suc (suc (suc zero))

putnam-2025-a4 : Set1
putnam-2025-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  IsLeastDimension reals three
