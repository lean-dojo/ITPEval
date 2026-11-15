-- Statement-only formalization of "Euler's Summation of 1 + (1/2)^2 + (1/3)^2 + ..."
-- from Hundred Theorems item 014: the reciprocal-square series converges to pi squared
-- divided by 6. This file contains no proof.

module BaselSeries where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
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
      (x y z : R) -> add (add x y) z == add x (add y z)
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
      Either (lessOrEqual x y) (lessOrEqual y x)
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
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

differenceQuotient :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals f x y =
  divide reals
    (subtract reals (f y) (f x))
    (subtract reals y x)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals f x derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          StrictLess reals (subtract reals x delta) y ->
          StrictLess reals y (add reals x delta) ->
          y != x ->
          Both
            (StrictLess reals
              (subtract reals derivative epsilon)
              (differenceQuotient reals f x y))
            (StrictLess reals
              (differenceQuotient reals f x y)
              (add reals derivative epsilon))))

record StandardRealAnalysis (R : Set) : Set1 where
  field
    algebra : CompleteOrderedField R
    pi : R
    sine cosine : R -> R

    sine-zero :
      sine (zeroR algebra) == zeroR algebra
    cosine-zero :
      cosine (zeroR algebra) == oneR algebra
    sine-addition :
      (x y : R) ->
      sine (add algebra x y) ==
      add algebra
        (multiply algebra (sine x) (cosine y))
        (multiply algebra (cosine x) (sine y))
    cosine-addition :
      (x y : R) ->
      cosine (add algebra x y) ==
      subtract algebra
        (multiply algebra (cosine x) (cosine y))
        (multiply algebra (sine x) (sine y))
    sine-negate :
      (x : R) ->
      sine (negate algebra x) == negate algebra (sine x)
    cosine-negate :
      (x : R) ->
      cosine (negate algebra x) == cosine x
    pythagorean :
      (x : R) ->
      add algebra
        (square algebra (sine x))
        (square algebra (cosine x))
      == oneR algebra
    sine-derivative-at-zero :
      DerivativeAt algebra sine (zeroR algebra) (oneR algebra)

    pi-positive :
      StrictLess algebra (zeroR algebra) pi
    sine-pi :
      sine pi == zeroR algebra
    cosine-pi :
      cosine pi == negate algebra (oneR algebra)
    sine-positive-before-pi :
      (x : R) ->
      StrictLess algebra (zeroR algebra) x ->
      StrictLess algebra x pi ->
      StrictLess algebra (zeroR algebra) (sine x)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
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
      Both
        (StrictLess reals
          (subtract reals limit epsilon)
          (sequence n))
        (StrictLess reals
          (sequence n)
          (add reals limit epsilon)))

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals term limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n term)
    limit

reciprocalSquareTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
reciprocalSquareTerm reals n =
  divide reals
    (oneR reals)
    (square reals (fromNat reals (suc n)))

module Statement
  {R : Set}
  (reals : StandardRealAnalysis R) where

  open StandardRealAnalysis reals

  proposition : Set
  proposition =
    SeriesHasSum algebra
      (reciprocalSquareTerm algebra)
      (divide algebra
        (square algebra pi)
        (fromNat algebra 6))

eulers-summation-of-reciprocal-squares : Set1
eulers-summation-of-reciprocal-squares =
  (R : Set) ->
  (reals : StandardRealAnalysis R) ->
  Statement.proposition reals
