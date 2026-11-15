-- Statement-only formalization of thousand-theorems corpus artifact Q1038716
-- (thousand-theorems__agda__Q1038716), "Identity theorem": analytic functions
-- on a preconnected set that agree arbitrarily near a point of the set agree
-- throughout the set. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1038716_identity_theorem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_ _≤N_
infixr 3 _×_

data Bottom : Set where

Not : Set → Set
Not A = A → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _×_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

data _≤N_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR inverseR absoluteR : R → R
    lessOrEqualR : R → R → Set
    fromNatR : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x
    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zero :
      (x : R) →
      addR x zeroR ≡ x
    add-inverse :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) →
      multiplyR x oneR ≡ x
    multiply-zero :
      (x : R) →
      multiplyR x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    inverse-zero :
      inverseR zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (inverseR x) ≡ oneR

    order-reflexive :
      (x : R) →
      lessOrEqualR x x
    order-transitive :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y
    order-total :
      (x y : R) →
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-order :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      lessOrEqualR zeroR oneR × (zeroR ≠ oneR)

    absolute-nonnegative :
      (x : R) →
      lessOrEqualR zeroR (absoluteR x)
    absolute-zero-only :
      (x : R) →
      absoluteR x ≡ zeroR →
      x ≡ zeroR
    absolute-add :
      (x y : R) →
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiply :
      (x y : R) →
      absoluteR (multiplyR x y) ≡
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zero :
      fromNatR zero ≡ zeroR
    fromNat-successor :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR
    characteristic-zero :
      (m n : Nat) →
      fromNatR m ≡ fromNatR n →
      m ≡ n

    archimedean :
      (x : R) →
      Σ Nat (λ n → lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R → Set) →
      Σ R P →
      Σ R (λ upper → (x : R) → P x → lessOrEqualR x upper) →
      Σ R
        (λ supremum →
          ((x : R) → P x → lessOrEqualR x supremum)
          ×
          ((upper : R) →
            ((x : R) → P x → lessOrEqualR x upper) →
            lessOrEqualR supremum upper))

open CompleteOrderedField

StrictLess :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  lessOrEqualR reals x y × (x ≠ y)

Positive :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

record NormedField
  (R : Set)
  (reals : CompleteOrderedField R)
  (K : Set) : Set₁ where

  field
    zeroK oneK : K
    addK multiplyK : K → K → K
    negateK inverseK : K → K
    normK : K → R

    one-not-zeroK :
      oneK ≠ zeroK
    norm-greater-than-one :
      Σ K
        (λ x →
          StrictLess reals (oneR reals) (normK x))

    add-commutativeK :
      (x y : K) →
      addK x y ≡ addK y x
    add-associativeK :
      (x y z : K) →
      addK (addK x y) z ≡ addK x (addK y z)
    add-zeroK :
      (x : K) →
      addK x zeroK ≡ x
    add-inverseK :
      (x : K) →
      addK x (negateK x) ≡ zeroK

    multiply-commutativeK :
      (x y : K) →
      multiplyK x y ≡ multiplyK y x
    multiply-associativeK :
      (x y z : K) →
      multiplyK (multiplyK x y) z ≡
      multiplyK x (multiplyK y z)
    multiply-oneK :
      (x : K) →
      multiplyK x oneK ≡ x
    multiply-zeroK :
      (x : K) →
      multiplyK x zeroK ≡ zeroK
    distributeK :
      (x y z : K) →
      multiplyK x (addK y z) ≡
      addK (multiplyK x y) (multiplyK x z)
    inverse-zeroK :
      inverseK zeroK ≡ zeroK
    multiply-inverseK :
      (x : K) →
      x ≠ zeroK →
      multiplyK x (inverseK x) ≡ oneK

    norm-nonnegativeK :
      (x : K) →
      lessOrEqualR reals (zeroR reals) (normK x)
    norm-zeroK :
      normK zeroK ≡ zeroR reals
    norm-zero-onlyK :
      (x : K) →
      normK x ≡ zeroR reals →
      x ≡ zeroK
    norm-negateK :
      (x : K) →
      normK (negateK x) ≡ normK x
    norm-addK :
      (x y : K) →
      lessOrEqualR reals
        (normK (addK x y))
        (addR reals (normK x) (normK y))
    norm-multiplyK :
      (x y : K) →
      normK (multiplyK x y) ≡
      multiplyR reals (normK x) (normK y)

open NormedField

subtractK :
  {R K : Set} →
  {reals : CompleteOrderedField R} →
  NormedField R reals K →
  K →
  K →
  K
subtractK scalars x y =
  addK scalars x (negateK scalars y)

powerK :
  {R K : Set} →
  {reals : CompleteOrderedField R} →
  NormedField R reals K →
  K →
  Nat →
  K
powerK scalars x zero =
  oneK scalars
powerK scalars x (suc n) =
  multiplyK scalars x (powerK scalars x n)

record NormedSpace
  (R K E : Set)
  (reals : CompleteOrderedField R)
  (scalars : NormedField R reals K) : Set₁ where

  field
    zeroE : E
    addE : E → E → E
    negateE : E → E
    scaleE : K → E → E
    normE : E → R

    add-commutativeE :
      (x y : E) →
      addE x y ≡ addE y x
    add-associativeE :
      (x y z : E) →
      addE (addE x y) z ≡ addE x (addE y z)
    add-zeroE :
      (x : E) →
      addE x zeroE ≡ x
    add-inverseE :
      (x : E) →
      addE x (negateE x) ≡ zeroE

    scale-one :
      (x : E) →
      scaleE (oneK scalars) x ≡ x
    scale-associative :
      (a b : K) →
      (x : E) →
      scaleE (multiplyK scalars a b) x ≡
      scaleE a (scaleE b x)
    scale-add-vectors :
      (a : K) →
      (x y : E) →
      scaleE a (addE x y) ≡ addE (scaleE a x) (scaleE a y)
    scale-add-scalars :
      (a b : K) →
      (x : E) →
      scaleE (addK scalars a b) x ≡ addE (scaleE a x) (scaleE b x)

    norm-nonnegativeE :
      (x : E) →
      lessOrEqualR reals (zeroR reals) (normE x)
    norm-zeroE :
      normE zeroE ≡ zeroR reals
    norm-zero-onlyE :
      (x : E) →
      normE x ≡ zeroR reals →
      x ≡ zeroE
    norm-negateE :
      (x : E) →
      normE (negateE x) ≡ normE x
    norm-addE :
      (x y : E) →
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scaleE :
      (a : K) →
      (x : E) →
      normE (scaleE a x) ≡
      multiplyR reals (normK scalars a) (normE x)

open NormedSpace

subtractE :
  {R K E : Set} →
  {reals : CompleteOrderedField R} →
  {scalars : NormedField R reals K} →
  NormedSpace R K E reals scalars →
  E →
  E →
  E
subtractE space x y =
  addE space x (negateE space y)

SetOf : Set → Set₁
SetOf A = A → Set

Open :
  {R K : Set} →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  SetOf K →
  Set
Open {R = R} {K = K} reals scalars O =
  (x : K) →
  O x →
  Σ R
    (λ radius →
      Positive reals radius
      ×
      ((y : K) →
        StrictLess reals
          (normK scalars (subtractK scalars y x))
          radius →
        O y))

DisjointWithin :
  {A : Set} →
  SetOf A →
  SetOf A →
  SetOf A →
  Set
DisjointWithin {A = A} whole leftSet rightSet =
  (x : A) →
  whole x →
  leftSet x →
  rightSet x →
  Bottom

CoveredBy :
  {A : Set} →
  SetOf A →
  SetOf A →
  SetOf A →
  Set
CoveredBy {A = A} whole leftSet rightSet =
  (x : A) →
  whole x →
  Either (leftSet x) (rightSet x)

EmptyWithin :
  {A : Set} →
  SetOf A →
  SetOf A →
  Set
EmptyWithin {A = A} whole part =
  (x : A) →
  whole x →
  Not (part x)

Preconnected :
  {R K : Set} →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  SetOf K →
  Set₁
Preconnected {K = K} reals scalars U =
  (leftSet rightSet : SetOf K) →
  Open reals scalars leftSet →
  Open reals scalars rightSet →
  CoveredBy U leftSet rightSet →
  DisjointWithin U leftSet rightSet →
  Either
    (EmptyWithin U leftSet)
    (EmptyWithin U rightSet)

partialPowerSum :
  {R K E : Set} →
  {reals : CompleteOrderedField R} →
  {scalars : NormedField R reals K} →
  NormedSpace R K E reals scalars →
  (Nat → E) →
  K →
  Nat →
  E
partialPowerSum space coefficients displacement zero =
  zeroE space
partialPowerSum {scalars = scalars} space coefficients displacement (suc n) =
  addE space
    (partialPowerSum space coefficients displacement n)
    (scaleE space (powerK scalars displacement n) (coefficients n))

SequenceLimit :
  {R K E : Set} →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  (space : NormedSpace R K E reals scalars) →
  (Nat → E) →
  E →
  Set
SequenceLimit {R = R} reals scalars space sequence limit =
  (epsilon : R) →
  Positive reals epsilon →
  Σ Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤N n →
      StrictLess reals
        (normE space (subtractE space (sequence n) limit))
        epsilon)

HasPowerSeriesAt :
  {R K E : Set} →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  (space : NormedSpace R K E reals scalars) →
  (K → E) →
  K →
  (Nat → E) →
  R →
  Set
HasPowerSeriesAt {K = K} reals scalars space f center coefficients radius =
  Positive reals radius
  ×
  ((x : K) →
    StrictLess reals
      (normK scalars (subtractK scalars x center))
      radius →
    SequenceLimit reals scalars space
      (partialPowerSum space coefficients (subtractK scalars x center))
      (f x))

AnalyticAt :
  {R K E : Set} →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  (space : NormedSpace R K E reals scalars) →
  (K → E) →
  K →
  Set
AnalyticAt {R = R} {E = E} reals scalars space f center =
  Σ (Nat → E)
    (λ coefficients →
      Σ R
        (λ radius →
          HasPowerSeriesAt reals scalars space
            f center coefficients radius))

AnalyticOnNeighborhood :
  {R K E : Set} →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  (space : NormedSpace R K E reals scalars) →
  (K → E) →
  SetOf K →
  Set
AnalyticOnNeighborhood {K = K} reals scalars space f U =
  (x : K) →
  U x →
  AnalyticAt reals scalars space f x

FrequentlyEqualInPuncturedNeighborhood :
  {R K E : Set} →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  (K → E) →
  (K → E) →
  K →
  Set
FrequentlyEqualInPuncturedNeighborhood {R = R} {K = K}
  reals scalars f g center =
  (epsilon : R) →
  Positive reals epsilon →
  Σ K
    (λ x →
      (x ≠ center)
      ×
      (StrictLess reals
        (normK scalars (subtractK scalars x center))
        epsilon
      ×
      (f x ≡ g x)))

EqualOn :
  {K E : Set} →
  (K → E) →
  (K → E) →
  SetOf K →
  Set
EqualOn {K = K} f g U =
  (x : K) →
  U x →
  f x ≡ g x

identity-theorem : Set₁
identity-theorem =
  (R K E : Set) →
  (reals : CompleteOrderedField R) →
  (scalars : NormedField R reals K) →
  (space : NormedSpace R K E reals scalars) →
  (U : SetOf K) →
  (f g : K → E) →
  (center : K) →
  AnalyticOnNeighborhood reals scalars space f U →
  AnalyticOnNeighborhood reals scalars space g U →
  Preconnected reals scalars U →
  U center →
  FrequentlyEqualInPuncturedNeighborhood reals scalars f g center →
  EqualOn f g U
