-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_a1
-- (putnambench__agda__putnam_2023_a1): 18 is the least positive index whose
-- cosine product has second derivative at zero of absolute value above 2023.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023A1 where

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

AbsoluteLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
AbsoluteLess reals x bound =
  StrictLess reals (negate reals bound) x
  and
  StrictLess reals x bound

AbsoluteGreater :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
AbsoluteGreater reals x bound =
  StrictLess reals bound x
  or
  StrictLess reals x (negate reals bound)

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
      AbsoluteLess reals
        (subtract reals (sequence n) limit)
        epsilon)

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

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

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

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingSign reals zero =
  oneR reals
alternatingSign reals (suc n) =
  negate reals (alternatingSign reals n)

twoN : Nat
twoN =
  suc (suc zero)

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  multiply reals
    (alternatingSign reals n)
    (divide reals
      (naturalPower reals x (twoN * n))
      (fromNat reals (factorial (twoN * n))))

CosineValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
CosineValue reals x value =
  ConvergesTo reals
    (\ n ->
      sumFirst reals n
        (cosineTerm reals x))
    value

record StandardCosine
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    cosine : R -> R

    cosine-is-power-series :
      (x : R) ->
      CosineValue reals x (cosine x)

open StandardCosine

HasDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
HasDerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((h : R) ->
        AbsoluteLess reals h delta ->
        h != zeroR reals ->
        AbsoluteLess reals
          (subtract reals
            (divide reals
              (subtract reals
                (function (add reals point h))
                (function point))
              h)
            derivative)
          epsilon))

SecondDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
SecondDerivativeAt {R} reals function point secondDerivative =
  Exists (R -> R)
    (\ firstDerivative ->
      ((x : R) ->
        HasDerivativeAt reals function x (firstDerivative x))
      and
      HasDerivativeAt reals firstDerivative point secondDerivative)

cosineProduct :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardCosine reals ->
  Nat ->
  R ->
  R
cosineProduct reals analysis zero x =
  oneR reals
cosineProduct reals analysis (suc n) x =
  multiply reals
    (cosineProduct reals analysis n x)
    (cosine analysis
      (multiply reals
        (fromNat reals (suc n))
        x))

Positive : Nat -> Set
Positive n =
  suc zero <=N n

module Putnam2023A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardCosine reals) where

  Qualifies : Nat -> Set
  Qualifies n =
    Positive n
    and
    Exists R
      (\ secondDerivative ->
        SecondDerivativeAt reals
          (cosineProduct reals analysis n)
          (zeroR reals)
          secondDerivative
        and
        AbsoluteGreater reals
          secondDerivative
          (fromNat reals 2023))

  IsLeast : Nat -> Set
  IsLeast candidate =
    Qualifies candidate
    and
    ((n : Nat) ->
      Qualifies n ->
      candidate <=N n)

  proposition : Set
  proposition =
    IsLeast 18

putnam-2023-a1 : Set1
putnam-2023-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardCosine reals) ->
  Putnam2023A1Statement.proposition reals analysis
