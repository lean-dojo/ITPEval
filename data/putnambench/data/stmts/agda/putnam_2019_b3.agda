-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_b3
-- (putnambench__agda__putnam_2019_b3): a Householder reflection composed with
-- an orthogonal real matrix has eigenvalue one under the stated determinant
-- hypothesis. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2019B3 where

open import Agda.Builtin.Bool using (Bool; false; true)
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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

finEqual : {n : Nat} -> Fin n -> Fin n -> Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

select : {A : Set} -> Bool -> A -> A -> A
select true yes no =
  yes
select false yes no =
  no

Matrix : Set -> Nat -> Set
Matrix R n =
  Fin n -> Fin n -> R

Column : Set -> Nat -> Set
Column R n =
  Fin n -> Fin one -> R

MatrixEqual :
  {R : Set} {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Set
MatrixEqual A B =
  (i j : Fin _) ->
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

identityMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n
identityMatrix reals i j =
  select (finEqual i j)
    (oneR reals)
    (zeroR reals)

matrixSubtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixSubtract reals A B i j =
  add reals (A i j) (negate reals (B i j))

matrixScale :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  R ->
  Matrix R n ->
  Matrix R n
matrixScale reals scalar A i j =
  multiply reals scalar (A i j)

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

columnOuterProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Column R n ->
  Matrix R n
columnOuterProduct reals u i j =
  multiply reals (u i fzero) (u j fzero)

columnSquaredNorm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Column R n ->
  R
columnSquaredNorm reals u =
  sumFin reals
    (\ i -> multiply reals (u i fzero) (u i fzero))

rowDotProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Fin n ->
  Fin n ->
  R
rowDotProduct reals Q i j =
  sumFin reals
    (\ k -> multiply reals (Q i k) (Q j k))

columnDotProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Fin n ->
  Fin n ->
  R
columnDotProduct reals Q i j =
  sumFin reals
    (\ k -> multiply reals (Q k i) (Q k j))

Orthogonal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Set
Orthogonal reals {n} Q =
  ((i j : Fin n) ->
    i != j ->
    (rowDotProduct reals Q i j == zeroR reals)
    and
    (columnDotProduct reals Q i j == zeroR reals))
  and
  ((i : Fin n) ->
    (rowDotProduct reals Q i i == oneR reals)
    and
    (columnDotProduct reals Q i i == oneR reals))

reflectionMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Column R n ->
  Matrix R n
reflectionMatrix reals u =
  matrixSubtract reals
    (identityMatrix reals)
    (matrixScale reals
      (fromNat reals two)
      (columnOuterProduct reals u))

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
  {R : Set} {n : Nat} ->
  Matrix R (suc n) ->
  Fin (suc n) ->
  Matrix R n
firstRowMinor A removedColumn i j =
  A (fsuc i) (skip removedColumn j)

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Fin n ->
  R
alternatingSign reals fzero =
  oneR reals
alternatingSign reals (fsuc i) =
  negate reals (alternatingSign reals i)

determinant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  R
determinant reals {zero} A =
  oneR reals
determinant reals {suc n} A =
  sumFin reals
    (\ column ->
      multiply reals
        (alternatingSign reals column)
        (multiply reals
          (A fzero column)
          (determinant reals (firstRowMinor A column))))

putnam-2019-b3 : Set1
putnam-2019-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  (Q : Matrix R n) ->
  Orthogonal reals Q ->
  (u : Column R n) ->
  columnSquaredNorm reals u == oneR reals ->
  (P : Matrix R n) ->
  MatrixEqual P (reflectionMatrix reals u) ->
  determinant reals
    (matrixSubtract reals Q (identityMatrix reals))
    != zeroR reals ->
  determinant reals
    (matrixSubtract reals
      (matrixMultiply reals P Q)
      (identityMatrix reals))
    == zeroR reals
