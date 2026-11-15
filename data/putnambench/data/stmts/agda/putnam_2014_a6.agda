-- Statement-only formalization of PutnamBench corpus artifact putnam_2014_a6
-- (putnambench__agda__putnam_2014_a6): the largest number of pairs of real
-- square matrices whose cross-products have a zero diagonal entry exactly
-- off the matching indices is n raised to the nth power. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2014A6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

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
        (\ n ->
          lessOrEqual x (fromNat n))
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

Positive : Nat -> Set
Positive n =
  oneN <=N n

power : Nat -> Nat -> Nat
power base zero =
  oneN
power base (suc exponent) =
  base * power base exponent

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

matrixProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixProduct reals M N i j =
  sumFin reals
    (\ p ->
      multiply reals
        (M i p)
        (N p j))

HasZeroDiagonalEntry :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Set
HasZeroDiagonalEntry {R} reals {n} A =
  Exists (Fin n)
    (\ p ->
      A p p == zeroR reals)

Admissible :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  Set
Admissible {R} reals n k =
  Exists (Fin k -> Matrix R n)
    (\ M ->
      Exists (Fin k -> Matrix R n)
        (\ N ->
          (i j : Fin k) ->
          HasZeroDiagonalEntry reals
            (matrixProduct reals (M i) (N j))
          iff
          i != j))

IsLargestAdmissible :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  Set
IsLargestAdmissible reals n maximum =
  Positive maximum
  and
  Admissible reals n maximum
  and
  ((k : Nat) ->
    Positive k ->
    Admissible reals n k ->
    k <=N maximum)

putnam-2014-a6 : Set1
putnam-2014-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  IsLargestAdmissible reals n (power n n)
