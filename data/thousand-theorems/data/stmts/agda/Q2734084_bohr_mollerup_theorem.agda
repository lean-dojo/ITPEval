-- Statement-only formalization of thousand-theorems corpus artifact Q2734084,
-- "Bohr–Mollerup theorem": a positive log-convex real function normalized at
-- one and satisfying the Gamma functional equation agrees with the Gamma
-- function on the positive reals. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2734084_bohr_mollerup_theorem where

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

    absolute-negateR :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x

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
      Exists Nat
        (\ n ->
          lessOrEqualR x (fromNatR n))

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

Nonnegative :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqualR reals (zeroR reals) x

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

sumThrough :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumThrough reals terms zero =
  terms zero
sumThrough reals terms (suc n) =
  addR reals
    (sumThrough reals terms n)
    (terms (suc n))

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

logGammaSequence :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (logarithm : R -> R) ->
  R ->
  Nat ->
  R
logGammaSequence reals logarithm x n =
  subtractR reals
    (addR reals
      (multiplyR reals
        x
        (logarithm (fromNatR reals n)))
      (logarithm (fromNatR reals (factorial n))))
    (sumThrough reals
      (\ m ->
        logarithm
          (addR reals x (fromNatR reals m)))
      n)

record StandardGammaAnalysis
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    exponential logarithm gamma :
      R ->
      R

    exponential-series :
      (x : R) ->
      SequentialLimit reals
        (exponentialPartialSum reals x)
        (exponential x)

    exponential-positive :
      (x : R) ->
      Positive reals (exponential x)

    logarithm-zero :
      logarithm (zeroR reals) == zeroR reals

    logarithm-exponential :
      (x : R) ->
      logarithm (exponential x) == x

    exponential-logarithm :
      (x : R) ->
      Positive reals x ->
      exponential (logarithm x) == x

    gamma-positive :
      (x : R) ->
      Positive reals x ->
      Positive reals (gamma x)

    gamma-euler-limit :
      (x : R) ->
      Positive reals x ->
      SequentialLimit reals
        (logGammaSequence reals logarithm x)
        (logarithm (gamma x))

open StandardGammaAnalysis

ConvexLogOnPositive :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardGammaAnalysis reals ->
  (R -> R) ->
  Set
ConvexLogOnPositive {R = R} reals analysis f =
  (x y a b : R) ->
  Positive reals x ->
  Positive reals y ->
  Nonnegative reals a ->
  Nonnegative reals b ->
  addR reals a b == oneR reals ->
  lessOrEqualR reals
    (logarithm analysis
      (f
        (addR reals
          (multiplyR reals a x)
          (multiplyR reals b y))))
    (addR reals
      (multiplyR reals a (logarithm analysis (f x)))
      (multiplyR reals b (logarithm analysis (f y))))

bohr-mollerup-theorem : Set1
bohr-mollerup-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (analysis : StandardGammaAnalysis reals) ->
  (f : R -> R) ->
  ConvexLogOnPositive reals analysis f ->
  ((y : R) ->
    Positive reals y ->
    f (addR reals y (oneR reals)) ==
    multiplyR reals y (f y)) ->
  ((y : R) ->
    Positive reals y ->
    Positive reals (f y)) ->
  f (oneR reals) == oneR reals ->
  (x : R) ->
  Positive reals x ->
  f x == gamma analysis x
