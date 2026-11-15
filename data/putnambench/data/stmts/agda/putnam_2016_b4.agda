-- Statement-only formalization of PutnamBench corpus artifact putnam_2016_b4
-- (putnambench__agda__putnam_2016_b4): the expected determinant of A minus
-- its transpose for a uniformly random 2n by 2n zero-one matrix equals
-- (2n)! divided by 4^n n!. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2016B4 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_
infixr 5 _::_

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

Positive : Nat -> Set
Positive n =
  suc zero <=N n

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

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

lookup :
  {A : Set} {n : Nat} ->
  Vec A n ->
  Fin n ->
  A
lookup (x :: xs) fzero =
  x
lookup (x :: xs) (fsuc i) =
  lookup xs i

Matrix : Set -> Nat -> Set
Matrix R n =
  Fin n -> Fin n -> R

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

transpose :
  {R : Set} {n : Nat} ->
  Matrix R n ->
  Matrix R n
transpose A i j =
  A j i

matrixSubtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixSubtract reals A B i j =
  subtract reals (A i j) (B i j)

boolToReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Bool ->
  R
boolToReal reals false =
  zeroR reals
boolToReal reals true =
  oneR reals

BoolMatrix : Nat -> Nat -> Set
BoolMatrix rows columns =
  Vec (Vec Bool columns) rows

realMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  BoolMatrix n n ->
  Matrix R n
realMatrix reals A i j =
  boolToReal reals (lookup (lookup A i) j)

skewDifference :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  BoolMatrix n n ->
  Matrix R n
skewDifference reals A =
  matrixSubtract reals
    (realMatrix reals A)
    (transpose (realMatrix reals A))

sumAllBoolVectors :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Vec Bool n -> R) ->
  R
sumAllBoolVectors reals {zero} value =
  value []
sumAllBoolVectors reals {suc n} value =
  add reals
    (sumAllBoolVectors reals
      (\ tail -> value (false :: tail)))
    (sumAllBoolVectors reals
      (\ tail -> value (true :: tail)))

sumAllBoolMatrices :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {rows columns : Nat} ->
  (BoolMatrix rows columns -> R) ->
  R
sumAllBoolMatrices reals {rows = zero} value =
  value []
sumAllBoolMatrices reals {rows = suc rows} {columns} value =
  sumAllBoolVectors reals
    (\ row ->
      sumAllBoolMatrices reals
        (\ remainingRows ->
          value (row :: remainingRows)))

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN * twoN

matrixSize : Nat -> Nat
matrixSize n =
  twoN * n

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  oneN
naturalPower base (suc exponent) =
  base * naturalPower base exponent

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

matrixCount : Nat -> Nat
matrixCount n =
  naturalPower twoN
    (matrixSize n * matrixSize n)

expectedDeterminant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
expectedDeterminant reals n =
  divide reals
    (sumAllBoolMatrices reals
      {rows = matrixSize n}
      {columns = matrixSize n}
      (\ A ->
        determinant reals
          (skewDifference reals A)))
    (fromNat reals (matrixCount n))

putnam2016B4Solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
putnam2016B4Solution reals n =
  divide reals
    (fromNat reals
      (factorial (matrixSize n)))
    (multiply reals
      (fromNat reals
        (naturalPower fourN n))
      (fromNat reals
        (factorial n)))

putnam-2016-b4 : Set1
putnam-2016-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  expectedDeterminant reals n ==
  putnam2016B4Solution reals n
