-- Statement-only formalization of Thousand Theorems corpus artifact Q470877
-- (thousand-theorems__agda__Q470877), "Stirling's theorem": the factorial
-- ratio n! divided by sqrt(2n) * (n / e)^n converges to sqrt(pi).
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q470877_stirling_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

_!=_ :
  {A : Set} ->
  A ->
  A ->
  Set
x != y =
  Not (x == y)

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
  zero<=     : {n : Nat} -> zero <=N n
  succ<=succ : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR :
      R

    addR multiplyR :
      R ->
      R ->
      R

    negateR reciprocalR absoluteR :
      R ->
      R

    lessOrEqualR :
      R ->
      R ->
      Set

    fromNatR :
      Nat ->
      R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y == addR y x

    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)

    add-zeroR :
      (x : R) ->
      addR x zeroR == x

    add-inverseR :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y == multiplyR y x

    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)

    multiply-oneR :
      (x : R) ->
      multiplyR x oneR == x

    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR == zeroR

    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)

    reciprocal-zeroR :
      reciprocalR zeroR == zeroR

    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) ->
      lessOrEqualR x x

    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z

    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y

    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)

    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)

    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)

    zero-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absolute-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR (absoluteR x)

    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x

    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x

    absolute-zero-onlyR :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR

    absolute-addR :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))

    absolute-multiplyR :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zeroR :
      fromNatR zero == zeroR

    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    fromNat-additionR :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)

    fromNat-multiplicationR :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)

    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (reciprocalR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

powerNatR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerNatR reals x zero =
  oneR reals
powerNatR reals x (suc n) =
  multiplyR reals (powerNatR reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R = R} reals sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (absoluteR reals
          (subtractR reals (sequence n) limit))
        epsilon)

alternating :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R ->
  R
alternating reals zero x =
  x
alternating reals (suc n) x =
  negateR reals (alternating reals n x)

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divideR reals
    (powerNatR reals x n)
    (fromNatR reals (factorial n))

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialPartialSum reals x zero =
  zeroR reals
exponentialPartialSum reals x (suc n) =
  addR reals
    (exponentialPartialSum reals x n)
    (exponentialTerm reals x n)

cosineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  alternating reals n
    (divideR reals
      (powerNatR reals x ((suc (suc zero)) * n))
      (fromNatR reals
        (factorial ((suc (suc zero)) * n))))

cosinePartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosinePartialSum reals x zero =
  zeroR reals
cosinePartialSum reals x (suc n) =
  addR reals
    (cosinePartialSum reals x n)
    (cosineTerm reals x n)

record StandardStirlingAnalysis
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    squareRoot cosine :
      R ->
      R

    exponentialOne halfPi :
      R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      lessOrEqualR reals (zeroR reals) (squareRoot x)

    square-root-square :
      (x : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      multiplyR reals (squareRoot x) (squareRoot x) == x

    exponential-one-series :
      SequentialLimit reals
        (exponentialPartialSum reals (oneR reals))
        exponentialOne

    cosine-series :
      (x : R) ->
      SequentialLimit reals
        (cosinePartialSum reals x)
        (cosine x)

    half-pi-positive :
      Positive reals halfPi

    cosine-half-pi-zero :
      cosine halfPi == zeroR reals

    half-pi-first-positive-zero :
      (x : R) ->
      Positive reals x ->
      cosine x == zeroR reals ->
      lessOrEqualR reals halfPi x

open StandardStirlingAnalysis

piR :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardStirlingAnalysis reals ->
  R
piR {reals = reals} analysis =
  addR reals (halfPi analysis) (halfPi analysis)

stirlingSequence :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardStirlingAnalysis reals ->
  Nat ->
  R
stirlingSequence {reals = reals} analysis n =
  divideR reals
    (fromNatR reals (factorial n))
    (multiplyR reals
      (squareRoot analysis
        (fromNatR reals ((suc (suc zero)) * n)))
      (powerNatR reals
        (divideR reals
          (fromNatR reals n)
          (exponentialOne analysis))
        n))

tendsto-stirlingSequence-square-root-pi : Set1
tendsto-stirlingSequence-square-root-pi =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (analysis : StandardStirlingAnalysis reals) ->
  SequentialLimit reals
    (stirlingSequence analysis)
    (squareRoot analysis (piR analysis))
