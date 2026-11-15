-- Statement-only formalization of PutnamBench corpus artifact putnam_2014_b2
-- (putnambench__agda__putnam_2014_b2): the greatest weighted integral for a
-- bounded real function on [1,3] with zero integral is log(4/3).
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Between :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
Between reals lower upper x =
  lessOrEqual reals lower x
  and
  lessOrEqual reals x upper

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

mesh :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Nat ->
  R
mesh reals lower upper pieces =
  divide reals
    (subtract reals upper lower)
    (fromNat reals pieces)

UniformTags :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (Nat -> Nat -> R) ->
  Set
UniformTags reals lower upper tags =
  (n i : Nat) ->
  i <N suc n ->
  Between reals
    (add reals lower
      (multiply reals
        (fromNat reals i)
        (mesh reals lower upper (suc n))))
    (add reals lower
      (multiply reals
        (fromNat reals (suc i))
        (mesh reals lower upper (suc n))))
    (tags n i)

uniformRiemannSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  (Nat -> R) ->
  Nat ->
  R
uniformRiemannSum reals lower upper function tags pieces =
  sumFirst reals pieces
    (\ i ->
      multiply reals
        (function (tags i))
        (mesh reals lower upper pieces))

IntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  Set
IntervalIntegralValue {R} reals lower upper function integralValue =
  (tags : Nat -> Nat -> R) ->
  UniformTags reals lower upper tags ->
  ConvergesTo reals
    (\ n ->
      uniformRiemannSum reals
        lower
        upper
        function
        (tags n)
        (suc n))
    integralValue

module Putnam2014B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

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

  one three fourThirds : R
  one =
    oneR reals
  three =
    fromNat reals threeN
  fourThirds =
    divide reals
      (fromNat reals fourN)
      three

  BoundedOnInterval : (R -> R) -> Set
  BoundedOnInterval function =
    (x : R) ->
    Between reals one three x ->
    lessOrEqual reals
      (negate reals one)
      (function x)
    and
    lessOrEqual reals
      (function x)
      one

  HasZeroIntegral : (R -> R) -> Set
  HasZeroIntegral function =
    IntervalIntegralValue reals
      one
      three
      function
      (zeroR reals)

  Admissible : (R -> R) -> Set
  Admissible function =
    BoundedOnInterval function
    and
    HasZeroIntegral function

  weightedFunction : (R -> R) -> R -> R
  weightedFunction function x =
    divide reals (function x) x

  HasWeightedIntegral :
    (R -> R) ->
    R ->
    Set
  HasWeightedIntegral function value =
    IntervalIntegralValue reals
      one
      three
      (weightedFunction function)
      value

  reciprocal : R -> R
  reciprocal x =
    divide reals one x

  IsLogFourThirds : R -> Set
  IsLogFourThirds value =
    IntervalIntegralValue reals
      one
      fourThirds
      reciprocal
      value

  record IsGreatestWeightedIntegral
    (maximum : R) :
    Set where

    field
      attained :
        Exists (R -> R)
          (\ function ->
            Admissible function
            and
            HasWeightedIntegral function maximum)

      upper-bound :
        (function : R -> R) ->
        (value : R) ->
        Admissible function ->
        HasWeightedIntegral function value ->
        lessOrEqual reals value maximum

  proposition : Set
  proposition =
    Exists R
      (\ maximum ->
        IsLogFourThirds maximum
        and
        IsGreatestWeightedIntegral maximum)

putnam-2014-b2 : Set1
putnam-2014-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2014B2Statement.proposition reals
