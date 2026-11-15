-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_b6
-- (putnambench__agda__putnam_2010_b6): equality of ordinary and entrywise
-- positive powers of a real square matrix, propagated from exponents 1 through
-- n + 1 to every positive exponent. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2010B6 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

select :
  {A : Set} ->
  Bool ->
  A ->
  A ->
  A
select true yes no =
  yes
select false yes no =
  no

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

identityMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n
identityMatrix reals i j =
  select (finEqual i j)
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
    (\ k ->
      multiply reals
        (A i k)
        (B k j))

matrixPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Nat ->
  Matrix R n
matrixPower reals A zero =
  identityMatrix reals
matrixPower reals A (suc k) =
  matrixMultiply reals A (matrixPower reals A k)

scalarPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
scalarPower reals x zero =
  oneR reals
scalarPower reals x (suc k) =
  multiply reals x (scalarPower reals x k)

entrywisePower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Nat ->
  Matrix R n
entrywisePower reals A k i j =
  scalarPower reals (A i j) k

oneN : Nat
oneN =
  suc zero

putnam-2010-b6 : Set1
putnam-2010-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  oneN <=N n ->
  (A : Matrix R n) ->
  (Apow : Nat -> Matrix R n) ->
  ((k : Nat) ->
    oneN <=N k ->
    MatrixEqual (Apow k) (entrywisePower reals A k)) ->
  ((k : Nat) ->
    oneN <=N k ->
    k <=N (n + oneN) ->
    MatrixEqual (matrixPower reals A k) (Apow k)) ->
  (k : Nat) ->
  oneN <=N k ->
  MatrixEqual (matrixPower reals A k) (Apow k)
