-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_b4
-- (putnambench__agda__putnam_2020_b4): the average reciprocal weight of
-- length-2n integer walks from zero back to zero, evaluated at n = 2020,
-- is 1 / 4040. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals base zero =
  oneR reals
naturalPower reals base (suc exponent) =
  multiply reals
    (naturalPower reals base exponent)
    base

integerPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Int ->
  R
integerPower reals base (pos exponent) =
  naturalPower reals base exponent
integerPower reals base (negsuc exponent) =
  inverse reals
    (naturalPower reals base (suc exponent))

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

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

intEqual : Int -> Int -> Bool
intEqual (pos m) (pos n) =
  natEqual m n
intEqual (pos m) (negsuc n) =
  false
intEqual (negsuc m) (pos n) =
  false
intEqual (negsuc m) (negsuc n) =
  natEqual m n

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

step : Bool -> Int
step false =
  negsuc zero
step true =
  pos (suc zero)

walkEndpointFrom :
  {n : Nat} ->
  Int ->
  Vec Bool n ->
  Int
walkEndpointFrom height [] =
  height
walkEndpointFrom height (direction :: remaining) =
  walkEndpointFrom
    (addInt height (step direction))
    remaining

walkEndpoint :
  {n : Nat} ->
  Vec Bool n ->
  Int
walkEndpoint =
  walkEndpointFrom (pos zero)

interiorPowerSumFrom :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Int ->
  Vec Bool n ->
  R
interiorPowerSumFrom reals height [] =
  zeroR reals
interiorPowerSumFrom reals height (direction :: []) =
  zeroR reals
interiorPowerSumFrom reals height
  (direction :: next-direction :: remaining) =
  let next-height = addInt height (step direction) in
  add reals
    (integerPower reals
      (fromNat reals (suc (suc (suc zero))))
      next-height)
    (interiorPowerSumFrom reals
      next-height
      (next-direction :: remaining))

walkWeight :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Vec Bool n ->
  R
walkWeight reals directions =
  add reals
    (oneR reals)
    (interiorPowerSumFrom reals (pos zero) directions)

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

sumAllBoolVectorsNat :
  {n : Nat} ->
  (Vec Bool n -> Nat) ->
  Nat
sumAllBoolVectorsNat {zero} value =
  value []
sumAllBoolVectorsNat {suc n} value =
  sumAllBoolVectorsNat
    (\ tail -> value (false :: tail))
  +
  sumAllBoolVectorsNat
    (\ tail -> value (true :: tail))

returningIndicator :
  {n : Nat} ->
  Vec Bool n ->
  Nat
returningIndicator directions
  with intEqual (walkEndpoint directions) (pos zero)
... | false =
  zero
... | true =
  suc zero

returningReciprocal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Vec Bool n ->
  R
returningReciprocal reals directions
  with intEqual (walkEndpoint directions) (pos zero)
... | false =
  zeroR reals
... | true =
  inverse reals (walkWeight reals directions)

walkLength : Nat -> Nat
walkLength n =
  (suc (suc zero)) * n

returningWalkCount : Nat -> Nat
returningWalkCount n =
  sumAllBoolVectorsNat
    {n = walkLength n}
    returningIndicator

returningReciprocalSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
returningReciprocalSum reals n =
  sumAllBoolVectors reals
    {n = walkLength n}
    (returningReciprocal reals)

walkAverage :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
walkAverage reals n =
  divide reals
    (returningReciprocalSum reals n)
    (fromNat reals (returningWalkCount n))

putnam-2020-b4-solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
putnam-2020-b4-solution reals =
  divide reals
    (oneR reals)
    (fromNat reals 4040)

putnam-2020-b4 : Set1
putnam-2020-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  walkAverage reals 2020 ==
  putnam-2020-b4-solution reals
