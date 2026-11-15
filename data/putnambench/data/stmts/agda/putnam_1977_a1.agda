-- Statement-only formalization of PutnamBench corpus artifact putnam_1977_a1:
-- four distinct points on the real quartic y = 2x^4 + 7x^3 + 3x - 5 that
-- lie on one line have average x-coordinate -7/8. This file contains no proof.

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

sixN : Nat
sixN =
  suc fiveN

sevenN : Nat
sevenN =
  suc sixN

eightN : Nat
eightN =
  suc sevenN

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
      multiply (multiply x y) z == multiply x (multiply y z)
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

quartic :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
quartic reals x =
  subtract reals
    (add reals
      (add reals
        (multiply reals
          (fromNat reals twoN)
          (naturalPower reals x fourN))
        (multiply reals
          (fromNat reals sevenN)
          (naturalPower reals x threeN)))
      (multiply reals
        (fromNat reals threeN)
        x))
    (fromNat reals fiveN)

FourDistinct :
  {R : Set} ->
  R ->
  R ->
  R ->
  R ->
  Set
FourDistinct x1 x2 x3 x4 =
  x1 != x2
  and
  x1 != x3
  and
  x1 != x4
  and
  x2 != x3
  and
  x2 != x4
  and
  x3 != x4

OnOneAffineLine :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  R ->
  Set
OnOneAffineLine {R} reals x1 x2 x3 x4 =
  Exists R
    (\ slope ->
      Exists R
        (\ intercept ->
          quartic reals x1 ==
            add reals (multiply reals slope x1) intercept
          and
          quartic reals x2 ==
            add reals (multiply reals slope x2) intercept
          and
          quartic reals x3 ==
            add reals (multiply reals slope x3) intercept
          and
          quartic reals x4 ==
            add reals (multiply reals slope x4) intercept))

sumFour :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  R ->
  R
sumFour reals x1 x2 x3 x4 =
  add reals
    (add reals (add reals x1 x2) x3)
    x4

averageFour :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  R ->
  R
averageFour reals x1 x2 x3 x4 =
  divide reals
    (sumFour reals x1 x2 x3 x4)
    (fromNat reals fourN)

minusSevenEighths :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
minusSevenEighths reals =
  divide reals
    (negate reals (fromNat reals sevenN))
    (fromNat reals eightN)

module Putnam1977A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (x1 x2 x3 x4 : R) ->
    FourDistinct x1 x2 x3 x4 ->
    OnOneAffineLine reals x1 x2 x3 x4 ->
    averageFour reals x1 x2 x3 x4 ==
    minusSevenEighths reals

putnam-1977-a1 : Set1
putnam-1977-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1977A1Statement.proposition reals
