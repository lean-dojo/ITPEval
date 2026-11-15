-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_b6:
-- a finite group of real square matrices whose traces sum to zero has matrix
-- sum equal to the zero matrix. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; true; false)
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

finEqual :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

ifThenElse :
  {A : Set} ->
  Bool ->
  A ->
  A ->
  A
ifThenElse true when-true when-false =
  when-true
ifThenElse false when-true when-false =
  when-false

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
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
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

Matrix :
  Set ->
  Nat ->
  Set
Matrix R n =
  Fin n -> Fin n -> R

MatrixEqual :
  {R : Set} {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Set
MatrixEqual {n = n} A B =
  (i j : Fin n) ->
  A i j == B i j

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

zeroMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n
zeroMatrix reals i j =
  zeroR reals

identityMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n
identityMatrix reals i j =
  ifThenElse
    (finEqual i j)
    (oneR reals)
    (zeroR reals)

matrixMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixMultiply reals A B i j =
  sumFin reals
    (\ k -> multiply reals (A i k) (B k j))

trace :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  R
trace reals A =
  sumFin reals (\ i -> A i i)

record FiniteMatrixSet
  (R : Set)
  (n : Nat) :
  Set where

  field
    cardinality :
      Nat
    enumerate :
      Fin cardinality ->
      Matrix R n
    enumeration-injective :
      (i j : Fin cardinality) ->
      MatrixEqual (enumerate i) (enumerate j) ->
      i == j

open FiniteMatrixSet

matrixSum :
  {R : Set} {n : Nat} ->
  CompleteOrderedRealField R ->
  FiniteMatrixSet R n ->
  Matrix R n
matrixSum reals G i j =
  sumFin reals
    (\ k -> enumerate G k i j)

ClosedUnderMultiplication :
  {R : Set} {n : Nat} ->
  CompleteOrderedRealField R ->
  FiniteMatrixSet R n ->
  Set
ClosedUnderMultiplication reals G =
  (i j : Fin (cardinality G)) ->
  Exists (Fin (cardinality G))
    (\ k ->
      MatrixEqual
        (matrixMultiply reals (enumerate G i) (enumerate G j))
        (enumerate G k))

IdentityBelongs :
  {R : Set} {n : Nat} ->
  CompleteOrderedRealField R ->
  FiniteMatrixSet R n ->
  Set
IdentityBelongs reals G =
  Exists (Fin (cardinality G))
    (\ i ->
      MatrixEqual
        (enumerate G i)
        (identityMatrix reals))

RightInversesBelong :
  {R : Set} {n : Nat} ->
  CompleteOrderedRealField R ->
  FiniteMatrixSet R n ->
  Set
RightInversesBelong reals G =
  (i : Fin (cardinality G)) ->
  Exists (Fin (cardinality G))
    (\ j ->
      MatrixEqual
        (matrixMultiply reals (enumerate G i) (enumerate G j))
        (identityMatrix reals))

GroupUnderMultiplication :
  {R : Set} {n : Nat} ->
  CompleteOrderedRealField R ->
  FiniteMatrixSet R n ->
  Set
GroupUnderMultiplication reals G =
  ClosedUnderMultiplication reals G
  and
  IdentityBelongs reals G
  and
  RightInversesBelong reals G

putnam-1985-b6 : Set1
putnam-1985-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  (G : FiniteMatrixSet R n) ->
  GroupUnderMultiplication reals G ->
  sumFin reals
    (\ k -> trace reals (enumerate G k))
    == zeroR reals ->
  MatrixEqual
    (matrixSum reals G)
    (zeroMatrix reals)
