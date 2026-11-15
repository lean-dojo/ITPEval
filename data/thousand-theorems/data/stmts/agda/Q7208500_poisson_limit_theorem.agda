-- Statement-only formalization of Thousand Theorems corpus artifact Q7208500
-- (thousand-theorems__agda__Q7208500), "Poisson limit theorem": if n * p(n)
-- converges to r, then the corresponding binomial mass expression converges
-- to exp(-r) * r^k / k!. This file contains no proof.

{-# OPTIONS --safe #-}

module Q7208500_poisson_limit_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

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

natCast :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
natCast reals =
  fromNatR reals

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

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  oneR reals
powerR reals x (suc n) =
  multiplyR reals (powerR reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

choose : Nat -> Nat -> Nat
choose n zero =
  suc zero
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

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

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divideR reals
    (powerR reals x n)
    (natCast reals (factorial n))

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

record StandardExponential
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    exponential :
      R ->
      R

    exponential-series :
      (x : R) ->
      SequentialLimit reals
        (exponentialPartialSum reals x)
        (exponential x)

open StandardExponential

scaledParameterSequence :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
scaledParameterSequence reals p n =
  multiplyR reals
    (natCast reals n)
    (p n)

binomialMassExpression :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  Nat ->
  R
binomialMassExpression reals p k n =
  multiplyR reals
    (multiplyR reals
      (natCast reals (choose n k))
      (powerR reals (p n) k))
    (powerR reals
      (subtractR reals (oneR reals) (p n))
      (n - k))

poissonLimitValue :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardExponential reals ->
  R ->
  Nat ->
  R
poissonLimitValue {reals = reals} analysis r k =
  divideR reals
    (multiplyR reals
      (exponential analysis (negateR reals r))
      (powerR reals r k))
    (natCast reals (factorial k))

poisson-limit-theorem : Set1
poisson-limit-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (analysis : StandardExponential reals) ->
  (p : Nat -> R) ->
  (r : R) ->
  (k : Nat) ->
  SequentialLimit reals
    (scaledParameterSequence reals p)
    r ->
  SequentialLimit reals
    (binomialMassExpression reals p k)
    (poissonLimitValue analysis r k)
