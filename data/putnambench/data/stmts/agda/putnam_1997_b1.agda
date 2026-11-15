-- Statement-only formalization of PutnamBench corpus artifact putnam_1997_b1:
-- the sum from 1 through 6n - 1 of the smaller nearest-integer distance of
-- m/(6n) and m/(3n) equals n for every positive natural n. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

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

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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

minimum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
minimum reals x y with order-total reals x y
... | left _ =
  x
... | right _ =
  y

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

sumOneThrough :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumOneThrough reals n terms =
  sumFirst reals n (\ i -> terms (suc i))

record StandardIntegerParts
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    floor ceiling : R -> Int

    floor-lower :
      (x : R) ->
      lessOrEqual reals
        (fromInt reals (floor x))
        x
    floor-greatest :
      (x : R) ->
      (z : Int) ->
      lessOrEqual reals (fromInt reals z) x ->
      lessOrEqual reals
        (fromInt reals z)
        (fromInt reals (floor x))

    ceiling-upper :
      (x : R) ->
      lessOrEqual reals
        x
        (fromInt reals (ceiling x))
    ceiling-least :
      (x : R) ->
      (z : Int) ->
      lessOrEqual reals x (fromInt reals z) ->
      lessOrEqual reals
        (fromInt reals (ceiling x))
        (fromInt reals z)

open StandardIntegerParts

oneN : Nat
oneN =
  suc zero

threeN : Nat
threeN =
  suc (suc oneN)

sixN : Nat
sixN =
  threeN + threeN

module Putnam1997B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (integerParts : StandardIntegerParts reals) where

  nearestIntegerDistance : R -> R
  nearestIntegerDistance x =
    minimum reals
      (subtract reals
        x
        (fromInt reals (floor integerParts x)))
      (subtract reals
        (fromInt reals (ceiling integerParts x))
        x)

  summand : Nat -> Nat -> R
  summand n m =
    minimum reals
      (nearestIntegerDistance
        (divide reals
          (fromNat reals m)
          (fromNat reals (sixN * n))))
      (nearestIntegerDistance
        (divide reals
          (fromNat reals m)
          (fromNat reals (threeN * n))))

  finiteSum : Nat -> R
  finiteSum n =
    sumOneThrough reals
      (sixN * n - oneN)
      (summand n)

  proposition : Set
  proposition =
    (n : Nat) ->
    oneN <=N n ->
    finiteSum n == fromNat reals n

putnam-1997-b1 : Set1
putnam-1997-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (integerParts : StandardIntegerParts reals) ->
  Putnam1997B1Statement.proposition reals integerParts
