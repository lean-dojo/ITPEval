-- Statement-only formalization of thousand-theorems corpus artifact Q9993851,
-- "Lax-Milgram theorem": every bounded coercive bilinear form on a real Hilbert
-- space induces a continuous linear equivalence characterized by the form.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q9993851_lax_milgram_theorem where

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Exists1 (A : Set1) (P : A -> Set) : Set1 where
  constructor witness1
  field
    value1    : A
    property1 : P value1

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
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
      (x : R) -> lessOrEqualR x x
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
      (x y : R) -> Either (lessOrEqualR x y) (lessOrEqualR y x)
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
      (x : R) -> lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-onlyR :
      (x : R) -> absoluteR x == zeroR -> x == zeroR
    absolute-negateR :
      (x : R) -> absoluteR (negateR x) == absoluteR x
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
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
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

record RealInnerProductSpace
  (R V : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    scaleV : R -> V -> V
    normV : V -> R
    inner : V -> V -> R

    add-commutativeV :
      (x y : V) -> addV x y == addV y x
    add-associativeV :
      (x y z : V) ->
      addV (addV x y) z == addV x (addV y z)
    add-zeroV :
      (x : V) -> addV x zeroV == x
    add-inverseV :
      (x : V) -> addV x (negateV x) == zeroV

    scale-oneV :
      (x : V) -> scaleV (oneR reals) x == x
    scale-associativeV :
      (a b : R) ->
      (x : V) ->
      scaleV (multiplyR reals a b) x == scaleV a (scaleV b x)
    scale-add-vectorsV :
      (a : R) ->
      (x y : V) ->
      scaleV a (addV x y) == addV (scaleV a x) (scaleV a y)
    scale-add-scalarsV :
      (a b : R) ->
      (x : V) ->
      scaleV (addR reals a b) x == addV (scaleV a x) (scaleV b x)

    norm-nonnegativeV :
      (x : V) ->
      lessOrEqualR reals (zeroR reals) (normV x)
    norm-zeroV :
      normV zeroV == zeroR reals
    norm-zero-onlyV :
      (x : V) -> normV x == zeroR reals -> x == zeroV
    norm-negateV :
      (x : V) -> normV (negateV x) == normV x
    norm-addV :
      (x y : V) ->
      lessOrEqualR reals
        (normV (addV x y))
        (addR reals (normV x) (normV y))
    norm-scaleV :
      (a : R) ->
      (x : V) ->
      normV (scaleV a x) ==
      multiplyR reals (absoluteR reals a) (normV x)

    inner-add-left :
      (x y z : V) ->
      inner (addV x y) z ==
      addR reals (inner x z) (inner y z)
    inner-scale-left :
      (a : R) ->
      (x y : V) ->
      inner (scaleV a x) y ==
      multiplyR reals a (inner x y)
    inner-add-right :
      (x y z : V) ->
      inner x (addV y z) ==
      addR reals (inner x y) (inner x z)
    inner-scale-right :
      (a : R) ->
      (x y : V) ->
      inner x (scaleV a y) ==
      multiplyR reals a (inner x y)
    inner-symmetric :
      (x y : V) ->
      inner x y == inner y x
    inner-nonnegative :
      (x : V) ->
      lessOrEqualR reals (zeroR reals) (inner x x)
    inner-definite :
      (x : V) ->
      inner x x == zeroR reals ->
      x == zeroV
    inner-norm-square :
      (x : V) ->
      multiplyR reals (normV x) (normV x) == inner x x

open RealInnerProductSpace

distanceV :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R V reals ->
  V ->
  V ->
  R
distanceV space x y =
  normV space (addV space x (negateV space y))

SequentialLimit :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R V reals ->
  (Nat -> V) ->
  V ->
  Set
SequentialLimit {R = R} {reals = reals} space sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distanceV space (sequence n) limit) epsilon)

CauchySequence :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R V reals ->
  (Nat -> V) ->
  Set
CauchySequence {R = R} {reals = reals} space sequence =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      StrictLess reals
        (distanceV space (sequence m) (sequence n))
        epsilon)

Complete :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R V reals ->
  Set
Complete {V = V} space =
  (sequence : Nat -> V) ->
  CauchySequence space sequence ->
  Exists V (\ limit -> SequentialLimit space sequence limit)

record ContinuousBilinearForm
  {R V : Set}
  {reals : CompleteOrderedField R}
  (space : RealInnerProductSpace R V reals) : Set1 where
  field
    apply : V -> V -> R
    map-add-left :
      (x y z : V) ->
      apply (addV space x y) z ==
      addR reals (apply x z) (apply y z)
    map-scale-left :
      (a : R) ->
      (x y : V) ->
      apply (scaleV space a x) y ==
      multiplyR reals a (apply x y)
    map-add-right :
      (x y z : V) ->
      apply x (addV space y z) ==
      addR reals (apply x y) (apply x z)
    map-scale-right :
      (a : R) ->
      (x y : V) ->
      apply x (scaleV space a y) ==
      multiplyR reals a (apply x y)

    operator-bound : R
    operator-bound-nonnegative :
      lessOrEqualR reals (zeroR reals) operator-bound
    operator-bound-property :
      (x y : V) ->
      lessOrEqualR reals
        (absoluteR reals (apply x y))
        (multiplyR reals operator-bound
          (multiplyR reals (normV space x) (normV space y)))

open ContinuousBilinearForm

Coercive :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : RealInnerProductSpace R V reals} ->
  ContinuousBilinearForm space ->
  Set
Coercive {R = R} {V = V} {reals = reals} {space = space} form =
  Exists R
    (\ constant ->
      Both
        (Positive reals constant)
        ((x : V) ->
          lessOrEqualR reals
            (multiplyR reals constant
              (multiplyR reals (normV space x) (normV space x)))
            (apply form x x)))

record ContinuousLinearEquivalence
  {R V : Set}
  {reals : CompleteOrderedField R}
  (space : RealInnerProductSpace R V reals) : Set1 where
  field
    forward backward : V -> V

    forward-map-add :
      (x y : V) ->
      forward (addV space x y) ==
      addV space (forward x) (forward y)
    forward-map-scale :
      (a : R) ->
      (x : V) ->
      forward (scaleV space a x) ==
      scaleV space a (forward x)
    backward-map-add :
      (x y : V) ->
      backward (addV space x y) ==
      addV space (backward x) (backward y)
    backward-map-scale :
      (a : R) ->
      (x : V) ->
      backward (scaleV space a x) ==
      scaleV space a (backward x)

    forward-bound backward-bound : R
    forward-bound-nonnegative :
      lessOrEqualR reals (zeroR reals) forward-bound
    backward-bound-nonnegative :
      lessOrEqualR reals (zeroR reals) backward-bound
    forward-bounded :
      (x : V) ->
      lessOrEqualR reals
        (normV space (forward x))
        (multiplyR reals forward-bound (normV space x))
    backward-bounded :
      (x : V) ->
      lessOrEqualR reals
        (normV space (backward x))
        (multiplyR reals backward-bound (normV space x))

    backward-after-forward :
      (x : V) -> backward (forward x) == x
    forward-after-backward :
      (x : V) -> forward (backward x) == x

open ContinuousLinearEquivalence

lax-milgram-theorem : Set1
lax-milgram-theorem =
  (R V : Set) ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace R V reals) ->
  Complete space ->
  (form : ContinuousBilinearForm space) ->
  Coercive form ->
  Exists1 (ContinuousLinearEquivalence space)
    (\ equivalence ->
      (v w : V) ->
      inner space (forward equivalence v) w == apply form v w)
