-- Statement-only formalization of thousand-theorems corpus artifact Q859122,
-- "Cauchy–Hadamard theorem": for a formal multilinear series, the inverse of
-- its convergence radius equals the limsup of the nth roots of its term norms.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q859122_cauchy_hadamard_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

record Top : Set where
  constructor top

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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

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
    negateR reciprocalR : R -> R
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

record NontriviallyNormedField
  {R K : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK reciprocalK : K -> K
    normK : K -> R

    one-not-zeroK :
      oneK != zeroK
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
    norm-addK :
      (x y : K) ->
      lessOrEqualR reals
        (normK (addK x y))
        (addR reals (normK x) (normK y))
    norm-multiplyK :
      (x y : K) ->
      normK (multiplyK x y) ==
      multiplyR reals (normK x) (normK y)
    norm-nontrivialK :
      Exists K
        (\ x ->
          Both
            (lessOrEqualR reals (oneR reals) (normK x))
            (oneR reals != normK x))

open NontriviallyNormedField

record NormedSpace
  {R K X : Set}
  (reals : CompleteOrderedField R)
  (scalars : NontriviallyNormedField {R = R} {K = K} reals) : Set1 where
  field
    zeroX : X
    addX : X -> X -> X
    negateX : X -> X
    scaleX : K -> X -> X
    normX : X -> R

    add-commutativeX :
      (x y : X) -> addX x y == addX y x
    add-associativeX :
      (x y z : X) ->
      addX (addX x y) z == addX x (addX y z)
    add-zeroX :
      (x : X) -> addX x zeroX == x
    add-inverseX :
      (x : X) -> addX x (negateX x) == zeroX

    scale-oneX :
      (x : X) ->
      scaleX (oneK scalars) x == x
    scale-associativeX :
      (a b : K) ->
      (x : X) ->
      scaleX (multiplyK scalars a b) x ==
      scaleX a (scaleX b x)
    scale-add-vectorsX :
      (a : K) ->
      (x y : X) ->
      scaleX a (addX x y) ==
      addX (scaleX a x) (scaleX a y)
    scale-add-scalarsX :
      (a b : K) ->
      (x : X) ->
      scaleX (addK scalars a b) x ==
      addX (scaleX a x) (scaleX b x)

    norm-nonnegativeX :
      (x : X) ->
      lessOrEqualR reals (zeroR reals) (normX x)
    norm-zeroX :
      normX zeroX == zeroR reals
    norm-zero-onlyX :
      (x : X) ->
      normX x == zeroR reals ->
      x == zeroX
    norm-addX :
      (x y : X) ->
      lessOrEqualR reals
        (normX (addX x y))
        (addR reals (normX x) (normX y))
    norm-scaleX :
      (a : K) ->
      (x : X) ->
      normX (scaleX a x) ==
      multiplyR reals (normK scalars a) (normX x)

open NormedSpace

data Vec (A : Set) : Nat -> Set where
  []  : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

Curried :
  Set ->
  Set ->
  Nat ->
  Set
Curried E F zero =
  F
Curried E F (suc n) =
  E -> Curried E F n

applyCurried :
  {E F : Set} ->
  {n : Nat} ->
  Curried E F n ->
  Vec E n ->
  F
applyCurried {n = zero} value [] =
  value
applyCurried {n = suc n} function (x :: xs) =
  applyCurried (function x) xs

record LinearAtHead
  {R K E F : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField {R = R} {K = K} reals}
  (source : NormedSpace {R = R} {K = K} {X = E} reals scalars)
  (target : NormedSpace {R = R} {K = K} {X = F} reals scalars)
  (n : Nat)
  (function : E -> Curried E F n) : Set where
  field
    map-add-head :
      (x y : E) ->
      (remaining : Vec E n) ->
      applyCurried (function (addX source x y)) remaining ==
      addX target
        (applyCurried (function x) remaining)
        (applyCurried (function y) remaining)
    map-scale-head :
      (a : K) ->
      (x : E) ->
      (remaining : Vec E n) ->
      applyCurried (function (scaleX source a x)) remaining ==
      scaleX target a (applyCurried (function x) remaining)

IsMultilinear :
  {R K E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  (source : NormedSpace {R = R} {K = K} {X = E} reals scalars) ->
  (target : NormedSpace {R = R} {K = K} {X = F} reals scalars) ->
  (n : Nat) ->
  Curried E F n ->
  Set
IsMultilinear source target zero value =
  Top
IsMultilinear source target (suc n) function =
  Both
    (LinearAtHead source target n function)
    ((x : _) ->
      IsMultilinear source target n (function x))

productNorm :
  {R K E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  (source : NormedSpace {R = R} {K = K} {X = E} reals scalars) ->
  {n : Nat} ->
  Vec E n ->
  R
productNorm {reals = reals} source [] =
  oneR reals
productNorm {reals = reals} source (x :: xs) =
  multiplyR reals (normX source x) (productNorm source xs)

record IsOperatorNorm
  {R K E F : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField {R = R} {K = K} reals}
  (source : NormedSpace {R = R} {K = K} {X = E} reals scalars)
  (target : NormedSpace {R = R} {K = K} {X = F} reals scalars)
  (n : Nat)
  (function : Curried E F n)
  (bound : R) : Set where
  field
    bound-nonnegative :
      lessOrEqualR reals (zeroR reals) bound
    bounds-function :
      (inputs : Vec E n) ->
      lessOrEqualR reals
        (normX target (applyCurried function inputs))
        (multiplyR reals bound (productNorm source inputs))
    least-bound :
      (candidate : R) ->
      lessOrEqualR reals (zeroR reals) candidate ->
      ((inputs : Vec E n) ->
        lessOrEqualR reals
          (normX target (applyCurried function inputs))
          (multiplyR reals candidate (productNorm source inputs))) ->
      lessOrEqualR reals bound candidate

record ContinuousMultilinearMap
  {R K E F : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField {R = R} {K = K} reals}
  (source : NormedSpace {R = R} {K = K} {X = E} reals scalars)
  (target : NormedSpace {R = R} {K = K} {X = F} reals scalars)
  (n : Nat) : Set1 where
  field
    functionN :
      Curried E F n
    multilinearN :
      IsMultilinear source target n functionN
    normN :
      R
    norm-characterizationN :
      IsOperatorNorm source target n functionN normN

open ContinuousMultilinearMap

FormalMultilinearSeries :
  {R K E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  NormedSpace {R = R} {K = K} {X = E} reals scalars ->
  NormedSpace {R = R} {K = K} {X = F} reals scalars ->
  Set1
FormalMultilinearSeries source target =
  (n : Nat) ->
  ContinuousMultilinearMap source target n

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

zeroNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  NonnegativeReal reals
zeroNN reals =
  nonnegative-real
    (zeroR reals)
    (order-reflexiveR reals (zeroR reals))

oneNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  NonnegativeReal reals
oneNN reals =
  nonnegative-real
    (oneR reals)
    (Both.first (zero-less-than-oneR reals))

record NonnegativeRoots
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    rootNN :
      NonnegativeReal reals ->
      Nat ->
      NonnegativeReal reals
    root-zero-degree :
      (x : NonnegativeReal reals) ->
      rootNN x zero == oneNN reals
    root-positive-power :
      (x : NonnegativeReal reals) ->
      (n : Nat) ->
      powerR reals (realValue (rootNN x (suc n))) (suc n) ==
      realValue x
    root-positive-unique :
      (x candidate : NonnegativeReal reals) ->
      (n : Nat) ->
      powerR reals (realValue candidate) (suc n) == realValue x ->
      realValue candidate == realValue (rootNN x (suc n))

open NonnegativeRoots

record ExtendedNonnegativeReals
  {R M : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroM oneM infinityM : M
    lessOrEqualM : M -> M -> Set
    finiteM : NonnegativeReal reals -> M
    inverseM : M -> M

    finite-zeroM :
      finiteM (zeroNN reals) == zeroM
    finite-oneM :
      finiteM (oneNN reals) == oneM
    finite-orderM :
      (x y : NonnegativeReal reals) ->
      Iff
        (lessOrEqualM (finiteM x) (finiteM y))
        (lessOrEqualR reals (realValue x) (realValue y))
    finite-injectiveM :
      (x y : NonnegativeReal reals) ->
      finiteM x == finiteM y ->
      realValue x == realValue y
    finite-le-infinityM :
      (x : NonnegativeReal reals) ->
      lessOrEqualM (finiteM x) infinityM
    infinity-not-finiteM :
      (x : NonnegativeReal reals) ->
      infinityM != finiteM x
    finite-or-infinityM :
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
    zero-leastM :
      (x : M) -> lessOrEqualM zeroM x
    infinity-greatestM :
      (x : M) -> lessOrEqualM x infinityM

    inverse-zeroM :
      inverseM zeroM == infinityM
    inverse-infinityM :
      inverseM infinityM == zeroM
    inverse-finite-nonzeroM :
      (x : NonnegativeReal reals) ->
      realValue x != zeroR reals ->
      Exists
        (lessOrEqualR reals
          (zeroR reals)
          (reciprocalR reals (realValue x)))
        (\ nonnegative-reciprocal ->
          inverseM (finiteM x) ==
          finiteM
            (nonnegative-real
              (reciprocalR reals (realValue x))
              nonnegative-reciprocal))

    supremumM :
      (M -> Set) ->
      M
    supremum-upperM :
      (P : M -> Set) ->
      (x : M) ->
      P x ->
      lessOrEqualM x (supremumM P)
    supremum-leastM :
      (P : M -> Set) ->
      (upper : M) ->
      ((x : M) -> P x -> lessOrEqualM x upper) ->
      lessOrEqualM (supremumM P) upper

    infimumM :
      (M -> Set) ->
      M
    infimum-lowerM :
      (P : M -> Set) ->
      (x : M) ->
      P x ->
      lessOrEqualM (infimumM P) x
    infimum-greatestM :
      (P : M -> Set) ->
      (lower : M) ->
      ((x : M) -> P x -> lessOrEqualM lower x) ->
      lessOrEqualM lower (infimumM P)

open ExtendedNonnegativeReals

TermNorm :
  {R K E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  {source : NormedSpace {R = R} {K = K} {X = E} reals scalars} ->
  {target : NormedSpace {R = R} {K = K} {X = F} reals scalars} ->
  FormalMultilinearSeries source target ->
  Nat ->
  NonnegativeReal reals
TermNorm {reals = reals} p n =
  nonnegative-real
    (normN (p n))
    (IsOperatorNorm.bound-nonnegative
      (norm-characterizationN (p n)))

BoundedAtRadius :
  {R K E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  {source : NormedSpace {R = R} {K = K} {X = E} reals scalars} ->
  {target : NormedSpace {R = R} {K = K} {X = F} reals scalars} ->
  FormalMultilinearSeries source target ->
  NonnegativeReal reals ->
  Set
BoundedAtRadius {R = R} {reals = reals} p radius =
  Exists R
    (\ bound ->
      (n : Nat) ->
      lessOrEqualR reals
        (multiplyR reals
          (realValue (TermNorm p n))
          (powerR reals (realValue radius) n))
        bound)

EligibleRadius :
  {R K E F M : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  {source : NormedSpace {R = R} {K = K} {X = E} reals scalars} ->
  {target : NormedSpace {R = R} {K = K} {X = F} reals scalars} ->
  (extended : ExtendedNonnegativeReals {R = R} {M = M} reals) ->
  FormalMultilinearSeries source target ->
  M ->
  Set
EligibleRadius extended p candidate =
  Exists
    (NonnegativeReal _)
    (\ radius ->
      Both
        (candidate == finiteM extended radius)
        (BoundedAtRadius p radius))

Radius :
  {R K E F M : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  {source : NormedSpace {R = R} {K = K} {X = E} reals scalars} ->
  {target : NormedSpace {R = R} {K = K} {X = F} reals scalars} ->
  (extended : ExtendedNonnegativeReals {R = R} {M = M} reals) ->
  FormalMultilinearSeries source target ->
  M
Radius extended p =
  supremumM extended (EligibleRadius extended p)

RootSequence :
  {R K E F M : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField {R = R} {K = K} reals} ->
  {source : NormedSpace {R = R} {K = K} {X = E} reals scalars} ->
  {target : NormedSpace {R = R} {K = K} {X = F} reals scalars} ->
  ExtendedNonnegativeReals {R = R} {M = M} reals ->
  NonnegativeRoots reals ->
  FormalMultilinearSeries source target ->
  Nat ->
  M
RootSequence extended roots p n =
  finiteM extended (rootNN roots (TermNorm p n) n)

EventuallyUpperBound :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals {R = R} {M = M} reals ->
  (Nat -> M) ->
  M ->
  Set
EventuallyUpperBound extended sequence upper =
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      lessOrEqualM extended (sequence n) upper)

LimsupAtTop :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals {R = R} {M = M} reals) ->
  (Nat -> M) ->
  M
LimsupAtTop extended sequence =
  infimumM extended (EventuallyUpperBound extended sequence)

cauchy-hadamard-theorem : Set1
cauchy-hadamard-theorem =
  (R K E F M : Set) ->
  (reals : CompleteOrderedField R) ->
  (scalars : NontriviallyNormedField {R = R} {K = K} reals) ->
  (source : NormedSpace {R = R} {K = K} {X = E} reals scalars) ->
  (target : NormedSpace {R = R} {K = K} {X = F} reals scalars) ->
  (extended : ExtendedNonnegativeReals {R = R} {M = M} reals) ->
  (roots : NonnegativeRoots reals) ->
  (p : FormalMultilinearSeries source target) ->
  inverseM extended (Radius extended p) ==
  LimsupAtTop extended (RootSequence extended roots p)
