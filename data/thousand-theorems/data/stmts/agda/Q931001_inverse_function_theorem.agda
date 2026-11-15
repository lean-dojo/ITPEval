-- Statement-only formalization of thousand-theorems corpus artifact Q931001,
-- "Inverse function theorem": a map between normed spaces whose strict
-- derivative at a point is a continuous linear equivalence has a local inverse
-- with the inverse strict derivative at the image point. This file contains no proof.

{-# OPTIONS --safe #-}

module Q931001_inverse_function_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

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
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
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
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
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

record NontriviallyNormedField
  (K R : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK reciprocalK : K -> K
    normK : K -> R

    one-not-zeroK :
      oneK != zeroK
    norm-nontrivialK :
      Exists K
        (\ x ->
          Both
            (lessOrEqualR reals (oneR reals) (normK x))
            (oneR reals != normK x))

    add-commutativeK :
      (x y : K) -> addK x y == addK y x
    add-associativeK :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-zeroK :
      (x : K) -> addK x zeroK == x
    add-inverseK :
      (x : K) -> addK x (negateK x) == zeroK

    multiply-commutativeK :
      (x y : K) -> multiplyK x y == multiplyK y x
    multiply-associativeK :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-oneK :
      (x : K) -> multiplyK x oneK == x
    multiply-zeroK :
      (x : K) -> multiplyK x zeroK == zeroK
    distributeK :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    reciprocal-zeroK :
      reciprocalK zeroK == zeroK
    multiply-reciprocalK :
      (x : K) ->
      x != zeroK ->
      multiplyK x (reciprocalK x) == oneK

    norm-nonnegativeK :
      (x : K) ->
      lessOrEqualR reals (zeroR reals) (normK x)
    norm-zeroK :
      normK zeroK == zeroR reals
    norm-zero-onlyK :
      (x : K) ->
      normK x == zeroR reals ->
      x == zeroK
    norm-negateK :
      (x : K) ->
      normK (negateK x) == normK x
    norm-addK :
      (x y : K) ->
      lessOrEqualR reals
        (normK (addK x y))
        (addR reals (normK x) (normK y))
    norm-multiplyK :
      (x y : K) ->
      normK (multiplyK x y) ==
      multiplyR reals (normK x) (normK y)

open NontriviallyNormedField

record NormedSpace
  (K R E : Set)
  (reals : CompleteOrderedField R)
  (scalars : NontriviallyNormedField K R reals) : Set1 where
  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : K -> E -> E
    normE : E -> R

    add-commutativeE :
      (x y : E) -> addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) -> addE x zeroE == x
    add-inverseE :
      (x : E) -> addE x (negateE x) == zeroE

    scale-oneE :
      (x : E) ->
      scaleE (oneK scalars) x == x
    scale-associativeE :
      (a b : K) ->
      (x : E) ->
      scaleE (multiplyK scalars a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectorsE :
      (a : K) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalarsE :
      (a b : K) ->
      (x : E) ->
      scaleE (addK scalars a b) x ==
      addE (scaleE a x) (scaleE b x)

    norm-nonnegativeE :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normE x)
    norm-zeroE :
      normE zeroE == zeroR reals
    norm-zero-onlyE :
      (x : E) ->
      normE x == zeroR reals ->
      x == zeroE
    norm-negateE :
      (x : E) ->
      normE (negateE x) == normE x
    norm-addE :
      (x y : E) ->
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scaleE :
      (a : K) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR reals (normK scalars a) (normE x)

open NormedSpace

subtractE :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R E reals scalars ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

distanceE :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R E reals scalars ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)

SequentialLimit :
  {R E : Set} ->
  CompleteOrderedField R ->
  (E -> E -> R) ->
  (Nat -> E) ->
  E ->
  Set
SequentialLimit {R = R} reals distance sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distance (sequence n) limit) epsilon)

CauchySequence :
  {R E : Set} ->
  CompleteOrderedField R ->
  (E -> E -> R) ->
  (Nat -> E) ->
  Set
CauchySequence {R = R} reals distance sequence =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      StrictLess reals (distance (sequence m) (sequence n)) epsilon)

Complete :
  {R E : Set} ->
  CompleteOrderedField R ->
  (E -> E -> R) ->
  Set
Complete {E = E} reals distance =
  (sequence : Nat -> E) ->
  CauchySequence reals distance sequence ->
  Exists E
    (\ limit ->
      SequentialLimit reals distance sequence limit)

record ContinuousLinearMap
  {K R E F : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField K R reals}
  (domain : NormedSpace K R E reals scalars)
  (codomain : NormedSpace K R F reals scalars) : Set where
  field
    apply : E -> F
    map-add :
      (x y : E) ->
      apply (addE domain x y) ==
      addE codomain (apply x) (apply y)
    map-scale :
      (a : K) ->
      (x : E) ->
      apply (scaleE domain a x) ==
      scaleE codomain a (apply x)
    operator-bound : R
    operator-bound-nonnegative :
      lessOrEqualR reals (zeroR reals) operator-bound
    bounded :
      (x : E) ->
      lessOrEqualR reals
        (normE codomain (apply x))
        (multiplyR reals operator-bound (normE domain x))

open ContinuousLinearMap

record ContinuousLinearEquivalence
  {K R E F : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField K R reals}
  (domain : NormedSpace K R E reals scalars)
  (codomain : NormedSpace K R F reals scalars) : Set where
  field
    forward :
      ContinuousLinearMap domain codomain
    inverse :
      ContinuousLinearMap codomain domain
    inverse-forward :
      (x : E) ->
      apply inverse (apply forward x) == x
    forward-inverse :
      (y : F) ->
      apply forward (apply inverse y) == y

open ContinuousLinearEquivalence

DerivativeRemainder :
  {K R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  (domain : NormedSpace K R E reals scalars) ->
  (codomain : NormedSpace K R F reals scalars) ->
  (E -> F) ->
  ContinuousLinearMap domain codomain ->
  E ->
  E ->
  F
DerivativeRemainder domain codomain function derivative x y =
  subtractE codomain
    (subtractE codomain (function x) (function y))
    (apply derivative (subtractE domain x y))

HasStrictFDerivAt :
  {K R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  (domain : NormedSpace K R E reals scalars) ->
  (codomain : NormedSpace K R F reals scalars) ->
  (E -> F) ->
  ContinuousLinearMap domain codomain ->
  E ->
  Set
HasStrictFDerivAt {R = R} {reals = reals}
  domain codomain function derivative point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((x y : _) ->
          StrictLess reals (distanceE domain x point) radius ->
          StrictLess reals (distanceE domain y point) radius ->
          lessOrEqualR reals
            (normE codomain
              (DerivativeRemainder
                domain codomain function derivative x y))
            (multiplyR reals epsilon
              (distanceE domain x y))))

LocallyLeftInverse :
  {K R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R E reals scalars ->
  (E -> F) ->
  (F -> E) ->
  E ->
  Set
LocallyLeftInverse {R = R} {reals = reals}
  domain function localInverse point =
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((x : _) ->
          StrictLess reals (distanceE domain x point) radius ->
          localInverse (function x) == x))

LocallyRightInverse :
  {K R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R F reals scalars ->
  (E -> F) ->
  (F -> E) ->
  E ->
  Set
LocallyRightInverse {R = R} {reals = reals}
  codomain function localInverse point =
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          StrictLess reals
            (distanceE codomain y (function point))
            radius ->
          function (localInverse y) == y))

inverse-function-theorem : Set1
inverse-function-theorem =
  (R K E F : Set) ->
  (reals : CompleteOrderedField R) ->
  (scalars : NontriviallyNormedField K R reals) ->
  (domain : NormedSpace K R E reals scalars) ->
  Complete reals (distanceE domain) ->
  (codomain : NormedSpace K R F reals scalars) ->
  (function : E -> F) ->
  (derivative : ContinuousLinearEquivalence domain codomain) ->
  (point : E) ->
  HasStrictFDerivAt
    domain codomain function (forward derivative) point ->
  Exists (F -> E)
    (\ localInverse ->
      Both
        (LocallyLeftInverse domain function localInverse point)
        (Both
          (LocallyRightInverse codomain function localInverse point)
          (HasStrictFDerivAt
            codomain domain localInverse (inverse derivative)
            (function point))))
