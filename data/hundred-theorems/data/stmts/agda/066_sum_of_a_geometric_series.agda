-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__066, "Sum of a Geometric Series": the finite
-- geometric-sum identity and, for real |r| < 1, convergence of the series
-- with terms a*r^n to a/(1-r). This file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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
  zero<=N : {n : Nat} -> zero <=N n
  suc<=N  : {m n : Nat} -> m <=N n -> suc m <=N suc n

record DivisionRing (D : Set) : Set1 where
  field
    zeroD oneD : D
    addD multiplyD : D -> D -> D
    negateD inverseD : D -> D

    oneD-not-zeroD :
      oneD != zeroD

    addD-commutative :
      (x y : D) -> addD x y == addD y x
    addD-associative :
      (x y z : D) -> addD (addD x y) z == addD x (addD y z)
    addD-zero-left :
      (x : D) -> addD zeroD x == x
    addD-zero-right :
      (x : D) -> addD x zeroD == x
    addD-inverse-left :
      (x : D) -> addD (negateD x) x == zeroD
    addD-inverse-right :
      (x : D) -> addD x (negateD x) == zeroD

    multiplyD-associative :
      (x y z : D) ->
      multiplyD (multiplyD x y) z == multiplyD x (multiplyD y z)
    multiplyD-one-left :
      (x : D) -> multiplyD oneD x == x
    multiplyD-one-right :
      (x : D) -> multiplyD x oneD == x
    multiplyD-zero-left :
      (x : D) -> multiplyD zeroD x == zeroD
    multiplyD-zero-right :
      (x : D) -> multiplyD x zeroD == zeroD
    distribute-left :
      (x y z : D) ->
      multiplyD x (addD y z) ==
      addD (multiplyD x y) (multiplyD x z)
    distribute-right :
      (x y z : D) ->
      multiplyD (addD x y) z ==
      addD (multiplyD x z) (multiplyD y z)
    multiplyD-inverse-left :
      (x : D) -> x != zeroD -> multiplyD (inverseD x) x == oneD
    multiplyD-inverse-right :
      (x : D) -> x != zeroD -> multiplyD x (inverseD x) == oneD
    inverseD-zero :
      inverseD zeroD == zeroD

subtractD :
  {D : Set} ->
  DivisionRing D ->
  D ->
  D ->
  D
subtractD division x y =
  DivisionRing.addD division x
    (DivisionRing.negateD division y)

divideD :
  {D : Set} ->
  DivisionRing D ->
  D ->
  D ->
  D
divideD division x y =
  DivisionRing.multiplyD division x
    (DivisionRing.inverseD division y)

powerD :
  {D : Set} ->
  DivisionRing D ->
  D ->
  Nat ->
  D
powerD division x zero =
  DivisionRing.oneD division
powerD division x (suc n) =
  DivisionRing.multiplyD division
    (powerD division x n)
    x

finiteSumD :
  {D : Set} ->
  DivisionRing D ->
  (Nat -> D) ->
  Nat ->
  D
finiteSumD division term zero =
  DivisionRing.zeroD division
finiteSumD division term (suc n) =
  DivisionRing.addD division
    (finiteSumD division term n)
    (term n)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR absoluteValueR : R -> R
    lessOrEqualR : R -> R -> Set

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR
    inverseR-zero :
      inverseR zeroR == zeroR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absoluteR-nonnegative :
      (x : R) -> lessOrEqualR zeroR (absoluteValueR x)
    absoluteR-of-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteValueR x == x
    absoluteR-of-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteValueR x == negateR x

    fromNatR : Nat -> R
    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-injective :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  CompleteOrderedField.addR reals x
    (CompleteOrderedField.negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  CompleteOrderedField.multiplyR reals x
    (CompleteOrderedField.inverseR reals y)

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  CompleteOrderedField.oneR reals
powerR reals x (suc n) =
  CompleteOrderedField.multiplyR reals
    (powerR reals x n)
    x

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both
    (CompleteOrderedField.lessOrEqualR reals x y)
    (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals
    (CompleteOrderedField.zeroR reals)
    x

partialSumR :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
partialSumR reals term zero =
  CompleteOrderedField.zeroR reals
partialSumR reals term (suc n) =
  CompleteOrderedField.addR reals
    (partialSumR reals term n)
    (term n)

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (CompleteOrderedField.absoluteValueR reals
          (subtractR reals (sequence n) limit))
        epsilon)

SeriesSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesSum reals term limit =
  SequentialLimit reals (partialSumR reals term) limit

record GeometricSeriesClaims : Set1 where
  field
    finite-geometric-sum :
      (D : Set) ->
      (division : DivisionRing D) ->
      (x : D) ->
      x != DivisionRing.oneD division ->
      (n : Nat) ->
      finiteSumD division (\ i -> powerD division x i) n ==
      divideD division
        (subtractD division
          (powerD division x n)
          (DivisionRing.oneD division))
        (subtractD division x (DivisionRing.oneD division))

    infinite-geometric-series :
      (R : Set) ->
      (reals : CompleteOrderedField R) ->
      (a r : R) ->
      StrictLess reals
        (CompleteOrderedField.absoluteValueR reals r)
        (CompleteOrderedField.oneR reals) ->
      SeriesSum reals
        (\ n ->
          CompleteOrderedField.multiplyR reals a
            (powerR reals r n))
        (divideR reals a
          (subtractR reals
            (CompleteOrderedField.oneR reals)
            r))

sum-of-a-geometric-series : Set1
sum-of-a-geometric-series =
  GeometricSeriesClaims
