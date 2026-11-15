-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_b5
-- (putnambench__agda__putnam_2019_b5): the degree-1008 real polynomial
-- interpolating odd-indexed Fibonacci numbers yields the unique positive
-- index pair (2019, 1010) in the stated difference equation. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixl 6 _+Z_ _-Z_
infixr 3 _and_

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
  left-choice  : A -> A or B
  right-choice : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Pair (A B : Set) : Set where
  constructor pair
  field
    left  : A
    right : B

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Positive : Nat -> Set
Positive n =
  oneN <=N n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_-Z_ : Int -> Int -> Int
x -Z y =
  x +Z negateInt y

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

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

record Polynomial
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set where

  field
    coefficient : Nat -> R
    degree      : Nat

    higher-coefficients-zero :
      (n : Nat) ->
      degree <N n ->
      coefficient n == zeroR reals

    leading-coefficient-nonzero :
      coefficient degree != zeroR reals

open Polynomial

evaluate :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  R ->
  R
evaluate reals polynomial x =
  sumFirst reals
    (suc (degree polynomial))
    (\ n ->
      multiply reals
        (coefficient polynomial n)
        (naturalPower reals x n))

FibonacciConditions :
  (Nat -> Int) ->
  Set
FibonacciConditions F =
  F oneN == pos oneN
  and
  F twoN == pos oneN
  and
  ((n : Nat) ->
    Positive n ->
    F (n + twoN) ==
    F (n + oneN) +Z F n)

InterpolationConditions :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (Nat -> Int) ->
  Polynomial reals ->
  Set
InterpolationConditions reals F polynomial =
  degree polynomial == 1008
  and
  ((n : Nat) ->
    n <=N 1008 ->
    evaluate reals polynomial
      (fromNat reals (twoN * n + oneN))
    ==
    fromInt reals (F (twoN * n + oneN)))

putnam-2019-b5-solution : Pair Nat Nat
putnam-2019-b5-solution =
  pair 2019 1010

SolutionEquation :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (Nat -> Int) ->
  Polynomial reals ->
  Nat ->
  Nat ->
  Set
SolutionEquation reals F polynomial j k =
  evaluate reals polynomial (fromNat reals 2019) ==
  fromInt reals (F j -Z F k)
  and
  Positive j
  and
  Positive k

putnam-2019-b5 : Set1
putnam-2019-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (F : Nat -> Int) ->
  (polynomial : Polynomial reals) ->
  FibonacciConditions F ->
  InterpolationConditions reals F polynomial ->
  (j k : Nat) ->
  Iff
    (SolutionEquation reals F polynomial j k)
    (pair j k == putnam-2019-b5-solution)
