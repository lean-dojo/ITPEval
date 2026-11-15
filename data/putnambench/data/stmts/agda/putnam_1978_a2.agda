-- Statement-only formalization of PutnamBench corpus artifact putnam_1978_a2:
-- the determinant of a real matrix with constant entries above and below the
-- diagonal is expressed using the product of its shifted diagonal entries.
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

data Comparison : Set where
  less    : Comparison
  equal   : Comparison
  greater : Comparison

compareFin :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Comparison
compareFin fzero fzero =
  equal
compareFin fzero (fsuc j) =
  less
compareFin (fsuc i) fzero =
  greater
compareFin (fsuc i) (fsuc j) =
  compareFin i j

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

productFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
productFin reals {zero} term =
  oneR reals
productFin reals {suc n} term =
  multiply reals
    (term fzero)
    (productFin reals (\ i -> term (fsuc i)))

Matrix : Set -> Nat -> Set
Matrix R n =
  Fin n -> Fin n -> R

skip :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skip {zero} column ()
skip {suc n} fzero k =
  fsuc k
skip {suc n} (fsuc column) fzero =
  fzero
skip {suc n} (fsuc column) (fsuc k) =
  fsuc (skip column k)

firstRowMinor :
  {R : Set} {n : Nat} ->
  Matrix R (suc n) ->
  Fin (suc n) ->
  Matrix R n
firstRowMinor A column i j =
  A (fsuc i) (skip column j)

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

putnamMatrix :
  {R : Set} {n : Nat} ->
  R ->
  R ->
  (Fin n -> R) ->
  Matrix R n
putnamMatrix a b c i j with compareFin i j
... | less =
  a
... | equal =
  c i
... | greater =
  b

shiftedDiagonalProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R ->
  R
shiftedDiagonalProduct reals c x =
  productFin reals (\ i -> subtract reals (c i) x)

closedForm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  R ->
  R ->
  (Fin n -> R) ->
  R
closedForm reals a b c =
  divide reals
    (subtract reals
      (multiply reals b (shiftedDiagonalProduct reals c a))
      (multiply reals a (shiftedDiagonalProduct reals c b)))
    (subtract reals b a)

module Putnam1978A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (n : Nat) ->
    Positive n ->
    (a b : R) ->
    a != b ->
    (c : Fin n -> R) ->
    determinant reals (putnamMatrix a b c)
    ==
    closedForm reals a b c

putnam-1978-a2 : Set1
putnam-1978-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1978A2Statement.proposition reals
