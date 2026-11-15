-- Statement-only formalization of PutnamBench corpus artifact putnam_1984_a3:
-- the punctured limit of a normalized determinant of the parity-patterned
-- 2n by 2n real matrix equals n squared times (a squared minus b squared).
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

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

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

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

data Parity : Set where
  even odd : Parity

oppositeParity : Parity -> Parity
oppositeParity even =
  odd
oppositeParity odd =
  even

parity : Nat -> Parity
parity zero =
  even
parity (suc n) =
  oppositeParity (parity n)

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

LimitAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
LimitAt {R} reals function limit point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals limit epsilon (function x)))

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

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

offDiagonalEntry :
  {R : Set} {n : Nat} ->
  R ->
  R ->
  Fin n ->
  Fin n ->
  R
offDiagonalEntry a b i j with parity (finToNat i + finToNat j)
... | even =
  a
... | odd =
  b

putnamMatrix :
  {R : Set} ->
  (n : Nat) ->
  R ->
  R ->
  R ->
  Matrix R (twoN * n)
putnamMatrix n a b x i j with compareFin i j
... | less =
  offDiagonalEntry a b i j
... | equal =
  x
... | greater =
  offDiagonalEntry a b i j

module Putnam1984A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  quotient :
    Nat ->
    R ->
    R ->
    R ->
    R
  quotient n a b x =
    divide reals
      (determinant reals (putnamMatrix n a b x))
      (naturalPower reals
        (subtract reals x a)
        ((twoN * n) - twoN))

  solution :
    Nat ->
    R ->
    R ->
    R
  solution n a b =
    multiply reals
      (naturalPower reals (fromNat reals n) twoN)
      (subtract reals
        (naturalPower reals a twoN)
        (naturalPower reals b twoN))

  proposition : Set
  proposition =
    (n : Nat) ->
    Positive n ->
    (a b : R) ->
    a != b ->
    LimitAt reals
      (quotient n a b)
      (solution n a b)
      a

putnam-1984-a3 : Set1
putnam-1984-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1984A3Statement.proposition reals
