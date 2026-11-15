-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_a4
-- (putnambench__agda__putnam_2015_a4): the greatest uniform lower bound of
-- the binary series selected by even floors on the real interval [0,1).
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

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

twoN : Nat
twoN =
  suc (suc zero)

fourN : Nat
fourN =
  twoN * twoN

sevenN : Nat
sevenN =
  suc (suc (suc fourN))

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

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

InHalfOpenUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InHalfOpenUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  StrictLess reals x (oneR reals)

EvenFloorOfNonnegative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
EvenFloorOfNonnegative reals y =
  Exists Nat
    (\ k ->
      lessOrEqual reals
        (fromNat reals (twoN * k))
        y
      and
      StrictLess reals
        y
        (fromNat reals (suc (twoN * k))))

reciprocalPowerOfTwo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
reciprocalPowerOfTwo reals n =
  divide reals
    (oneR reals)
    (naturalPower reals
      (fromNat reals twoN)
      (suc n))

PutnamTermAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R ->
  Set
PutnamTermAt reals x n term =
  (EvenFloorOfNonnegative reals
    (multiply reals
      (fromNat reals (suc n))
      x)
  and
  term == reciprocalPowerOfTwo reals n)
  or
  (Not
    (EvenFloorOfNonnegative reals
      (multiply reals
        (fromNat reals (suc n))
        x))
  and
  term == zeroR reals)

PutnamTermsAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  (Nat -> R) ->
  Set
PutnamTermsAt reals x terms =
  (n : Nat) ->
  PutnamTermAt reals x n (terms n)

SeriesValueAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
SeriesValueAt {R} reals x total =
  Exists (Nat -> R)
    (\ terms ->
      PutnamTermsAt reals x terms
      and
      SeriesHasSum reals terms total)

UniformLowerBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
UniformLowerBound {R} reals lower =
  (x : R) ->
  InHalfOpenUnitInterval reals x ->
  Exists R
    (\ total ->
      SeriesValueAt reals x total
      and
      lessOrEqual reals lower total)

fourSevenths :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
fourSevenths reals =
  divide reals
    (fromNat reals fourN)
    (fromNat reals sevenN)

IsGreatestUniformLowerBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
IsGreatestUniformLowerBound {R} reals greatest =
  UniformLowerBound reals greatest
  and
  ((lower : R) ->
    UniformLowerBound reals lower ->
    lessOrEqual reals lower greatest)

putnam-2015-a4 : Set1
putnam-2015-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  IsGreatestUniformLowerBound reals
    (fourSevenths reals)
