-- Statement-only formalization of thousand-theorems corpus artifact Q220680,
-- "Banach fixed-point theorem": a contraction on a complete extended metric
-- space, from a point with finite initial displacement, has a fixed point to
-- which its iterates converge with the stated geometric error bound. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q220680_banach_fixed_point_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> addR x y == addR y x
    add-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) -> addR x zeroR == x
    add-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) -> multiplyR x oneR == x
    multiply-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zero :
      reciprocalR zeroR == zeroR
    multiply-reciprocal :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

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
      (x y : R) -> Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injective :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedean :
      (x : R) -> Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set1 where
  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) -> forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) -> backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) == fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set2 where
  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

StrictLessR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLessR reals x y =
  Both (lessOrEqualR reals x y) (x != y)

record NonnegativeReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  constructor nonnegative-real
  field
    realValue :
      R
    realValue-nonnegative :
      lessOrEqualR reals (zeroR reals) realValue

open NonnegativeReal

record ExtendedNonnegativeReals
  (R M : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroNN oneNN :
      NonnegativeReal reals
    zeroNN-value :
      realValue zeroNN == zeroR reals
    oneNN-value :
      realValue oneNN == oneR reals

    addNN multiplyNN subtractNN divideNN :
      NonnegativeReal reals ->
      NonnegativeReal reals ->
      NonnegativeReal reals
    addNN-value :
      (x y : NonnegativeReal reals) ->
      realValue (addNN x y) ==
      addR reals (realValue x) (realValue y)
    multiplyNN-value :
      (x y : NonnegativeReal reals) ->
      realValue (multiplyNN x y) ==
      multiplyR reals (realValue x) (realValue y)
    subtractNN-of-le :
      (x y : NonnegativeReal reals) ->
      lessOrEqualR reals (realValue y) (realValue x) ->
      realValue (subtractNN x y) ==
      addR reals (realValue x) (negateR reals (realValue y))
    subtractNN-of-ge :
      (x y : NonnegativeReal reals) ->
      lessOrEqualR reals (realValue x) (realValue y) ->
      subtractNN x y == zeroNN
    divideNN-positive :
      (x y : NonnegativeReal reals) ->
      StrictLessR reals (zeroR reals) (realValue y) ->
      realValue (divideNN x y) ==
      multiplyR reals (realValue x) (reciprocalR reals (realValue y))

    zeroM oneM infinityM :
      M
    addM multiplyM subtractM divideM :
      M ->
      M ->
      M
    lessOrEqualM :
      M ->
      M ->
      Set
    finiteM :
      NonnegativeReal reals ->
      M

    zeroM-finite :
      zeroM == finiteM zeroNN
    oneM-finite :
      oneM == finiteM oneNN
    infinity-not-finite :
      (x : NonnegativeReal reals) ->
      infinityM != finiteM x
    finite-extensional :
      (x y : NonnegativeReal reals) ->
      realValue x == realValue y ->
      finiteM x == finiteM y
    finite-injective :
      (x y : NonnegativeReal reals) ->
      finiteM x == finiteM y ->
      realValue x == realValue y
    finite-or-infinity :
      (x : M) ->
      Either
        (x == infinityM)
        (Exists (NonnegativeReal reals) (\ y -> x == finiteM y))

    order-reflexiveM :
      (x : M) -> lessOrEqualM x x
    order-transitiveM :
      (x y z : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y z ->
      lessOrEqualM x z
    order-antisymmetricM :
      (x y : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y x ->
      x == y
    order-totalM :
      (x y : M) -> Either (lessOrEqualM x y) (lessOrEqualM y x)
    zero-leastM :
      (x : M) -> lessOrEqualM zeroM x
    infinity-greatestM :
      (x : M) -> lessOrEqualM x infinityM
    finite-orderM :
      (x y : NonnegativeReal reals) ->
      Iff
        (lessOrEqualM (finiteM x) (finiteM y))
        (lessOrEqualR reals (realValue x) (realValue y))

    finite-addM :
      (x y : NonnegativeReal reals) ->
      addM (finiteM x) (finiteM y) == finiteM (addNN x y)
    finite-multiplyM :
      (x y : NonnegativeReal reals) ->
      multiplyM (finiteM x) (finiteM y) == finiteM (multiplyNN x y)
    finite-subtractM :
      (x y : NonnegativeReal reals) ->
      subtractM (finiteM x) (finiteM y) == finiteM (subtractNN x y)
    finite-divideM :
      (x y : NonnegativeReal reals) ->
      divideM (finiteM x) (finiteM y) == finiteM (divideNN x y)

    add-infinity-leftM :
      (x : M) -> addM infinityM x == infinityM
    add-infinity-rightM :
      (x : M) -> addM x infinityM == infinityM
    multiply-zero-leftM :
      (x : M) -> multiplyM zeroM x == zeroM
    multiply-zero-rightM :
      (x : M) -> multiplyM x zeroM == zeroM
    multiply-infinity-positive-leftM :
      (x : NonnegativeReal reals) ->
      realValue x != zeroR reals ->
      multiplyM infinityM (finiteM x) == infinityM
    multiply-infinity-positive-rightM :
      (x : NonnegativeReal reals) ->
      realValue x != zeroR reals ->
      multiplyM (finiteM x) infinityM == infinityM

open ExtendedNonnegativeReals

StrictLessM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  M ->
  M ->
  Set
StrictLessM extended x y =
  Both (lessOrEqualM extended x y) (x != y)

record ExtendedMetricSpace
  {a : Level}
  {R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (A : Set a) : Set (lsuc a) where
  field
    edist :
      A ->
      A ->
      M
    edist-self :
      (x : A) ->
      edist x x == zeroM extended
    edist-symmetric :
      (x y : A) ->
      edist x y == edist y x
    edist-triangle :
      (x y z : A) ->
      lessOrEqualM extended
        (edist x z)
        (addM extended (edist x y) (edist y z))
    edist-eq-zero :
      (x y : A) ->
      Iff
        (edist x y == zeroM extended)
        (x == y)

open ExtendedMetricSpace

EventuallyAtTop :
  (Nat -> Set) ->
  Set
EventuallyAtTop P =
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      P n)

Tendsto :
  {a : Level} ->
  {R M : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  ExtendedMetricSpace extended A ->
  (Nat -> A) ->
  A ->
  Set
Tendsto {R = R} {reals = reals} {extended = extended}
  metric sequence limit =
  (epsilon : NonnegativeReal reals) ->
  StrictLessR reals (zeroR reals) (realValue epsilon) ->
  EventuallyAtTop
    (\ n ->
      StrictLessM extended
        (edist metric (sequence n) limit)
        (finiteM extended epsilon))

CauchySequence :
  {a : Level} ->
  {R M : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  ExtendedMetricSpace extended A ->
  (Nat -> A) ->
  Set
CauchySequence {R = R} {reals = reals} {extended = extended}
  metric sequence =
  (epsilon : NonnegativeReal reals) ->
  StrictLessR reals (zeroR reals) (realValue epsilon) ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      StrictLessM extended
        (edist metric (sequence m) (sequence n))
        (finiteM extended epsilon))

Complete :
  {a : Level} ->
  {R M : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  ExtendedMetricSpace extended A ->
  Set a
Complete {A = A} metric =
  (sequence : Nat -> A) ->
  CauchySequence metric sequence ->
  Exists A (\ limit -> Tendsto metric sequence limit)

ContractingWith :
  {a : Level} ->
  {R M : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  ExtendedMetricSpace extended A ->
  NonnegativeReal reals ->
  (A -> A) ->
  Set a
ContractingWith {A = A} {reals = reals} {extended = extended}
  metric constant function =
  Both
    (StrictLessR reals
      (realValue constant)
      (oneR reals))
    ((x y : A) ->
      lessOrEqualM extended
        (edist metric (function x) (function y))
        (multiplyM extended
          (finiteM extended constant)
          (edist metric x y)))

iterate :
  {a : Level} ->
  {A : Set a} ->
  (A -> A) ->
  Nat ->
  A ->
  A
iterate function zero x =
  x
iterate function (suc n) x =
  function (iterate function n x)

powerM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  M ->
  Nat ->
  M
powerM extended x zero =
  oneM extended
powerM extended x (suc n) =
  multiplyM extended (powerM extended x n) x

banach-fixed-point-theorem :
  (a : Level) ->
  Set (lsuc (lsuc lzero) ⊔ lsuc a)
banach-fixed-point-theorem a =
  (R M : Set) ->
  (A : Set a) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (metric : ExtendedMetricSpace extended A) ->
  Complete metric ->
  (constant : NonnegativeReal reals) ->
  (function : A -> A) ->
  ContractingWith metric constant function ->
  (start : A) ->
  edist metric start (function start) != infinityM extended ->
  Exists A
    (\ fixedPoint ->
      Both
        (function fixedPoint == fixedPoint)
        (Both
          (Tendsto metric
            (\ n -> iterate function n start)
            fixedPoint)
          ((n : Nat) ->
            lessOrEqualM extended
              (edist metric
                (iterate function n start)
                fixedPoint)
              (divideM extended
                (multiplyM extended
                  (edist metric start (function start))
                  (powerM extended
                    (finiteM extended constant)
                    n))
                (subtractM extended
                  (oneM extended)
                  (finiteM extended constant))))))
