-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_b5:
-- a 2n by n complex matrix whose nonzero left-kernel vectors cannot be
-- entirely real has real-part image equal to every real 2n-vector.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

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

Vector : Set -> Nat -> Set
Vector A n =
  Fin n -> A

Matrix : Set -> Nat -> Nat -> Set
Matrix A rows columns =
  Fin rows -> Fin columns -> A

rowTimesMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {rows columns : Nat} ->
  Vector (Complex R) rows ->
  Matrix (Complex R) rows columns ->
  Vector (Complex R) columns
rowTimesMatrix reals z M column =
  sumFinComplex reals
    (\ row ->
      complexMultiply reals
        (z row)
        (M row column))

matrixTimesColumn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {rows columns : Nat} ->
  Matrix (Complex R) rows columns ->
  Vector (Complex R) columns ->
  Vector (Complex R) rows
matrixTimesColumn reals M w row =
  sumFinComplex reals
    (\ column ->
      complexMultiply reals
        (M row column)
        (w column))

twoN : Nat
twoN =
  suc (suc zero)

LeftKernelCondition :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Matrix (Complex R) (twoN * n) n ->
  Set
LeftKernelCondition {R} reals n M =
  (z : Vector (Complex R) (twoN * n)) ->
  ((column : Fin n) ->
    rowTimesMatrix reals z M column == complexZero reals) ->
  Not
    ((row : Fin (twoN * n)) ->
      z row == complexZero reals) ->
  Exists (Fin (twoN * n))
    (\ row ->
      imaginaryPart (z row) != zeroR reals)

module Putnam1987B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (n : Nat) ->
    Positive n ->
    (M : Matrix (Complex R) (twoN * n) n) ->
    LeftKernelCondition reals n M ->
    (r : Vector R (twoN * n)) ->
    Exists (Vector (Complex R) n)
      (\ w ->
        (row : Fin (twoN * n)) ->
        realPart (matrixTimesColumn reals M w row) == r row)

putnam-1987-b5 : Set1
putnam-1987-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1987B5Statement.proposition reals
