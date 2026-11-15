-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_a4
-- (putnambench__agda__putnam_2005_a4): an all-ones rectangular submatrix of
-- a square plus-or-minus-one real matrix with orthogonal rows has area at
-- most the matrix dimension. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

Matrix : Set -> Nat -> Nat -> Set
Matrix R rows columns =
  Fin rows -> Fin columns -> R

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

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A = A} f =
  (x y : A) ->
  f x == f y ->
  x == y

PositiveNat : Nat -> Set
PositiveNat n =
  suc zero <=N n

PlusOrMinusOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
PlusOrMinusOne reals x =
  x == oneR reals
  or
  x == negate reals (oneR reals)

HasPlusOrMinusOneEntries :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n n ->
  Set
HasPlusOrMinusOneEntries reals H =
  (i j : _) ->
  PlusOrMinusOne reals (H i j)

HasOrthogonalRows :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n n ->
  Set
HasOrthogonalRows reals H =
  (i j : _) ->
  i != j ->
  sumFin reals
    (\ k ->
      multiply reals
        (H i k)
        (H j k))
  ==
  zeroR reals

DimensionBounds : Nat -> Nat -> Nat -> Set
DimensionBounds n a b =
  suc zero <=N a
  and
  a <=N n
  and
  suc zero <=N b
  and
  b <=N n

IsSubmatrix :
  {R : Set} ->
  {n a b : Nat} ->
  Matrix R n n ->
  Matrix R a b ->
  Set
IsSubmatrix {n = n} {a = a} {b = b} H S =
  Exists (Fin a -> Fin n)
    (\ selectedRows ->
      Injective selectedRows
      and
      Exists (Fin b -> Fin n)
        (\ selectedColumns ->
          Injective selectedColumns
          and
          ((i : Fin a) ->
            (j : Fin b) ->
            S i j ==
            H (selectedRows i) (selectedColumns j))))

HasOnlyOneEntries :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {a b : Nat} ->
  Matrix R a b ->
  Set
HasOnlyOneEntries reals {a = a} {b = b} S =
  (i : Fin a) ->
  (j : Fin b) ->
  S i j == oneR reals

module Putnam2005A4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (n : Nat)
  (H : Matrix R n n)
  (a b : Nat)
  (S : Matrix R a b) where

  proposition : Set
  proposition =
    PositiveNat n ->
    HasPlusOrMinusOneEntries reals H ->
    HasOrthogonalRows reals H ->
    DimensionBounds n a b ->
    IsSubmatrix H S ->
    HasOnlyOneEntries reals S ->
    a * b <=N n

putnam-2005-a4 : Set1
putnam-2005-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  (H : Matrix R n n) ->
  (a b : Nat) ->
  (S : Matrix R a b) ->
  Putnam2005A4Statement.proposition
    reals
    n
    H
    a
    b
    S
