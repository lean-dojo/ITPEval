-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__090, "Stirling's Formula": the factorial sequence
-- is asymptotically equivalent to sqrt(2*pi*n) * (n/e)^n over natural indices.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _≤N_

data Bottom : Set where

NotEqual :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
NotEqual x y = x ≡ y → Bottom

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left : A → Either A B
  right : B → Either A B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A → Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value : A
    property : P value

data _≤N_ : Nat → Nat → Set where
  zero≤N : {n : Nat} → zero ≤N n
  suc≤N : {m n : Nat} → m ≤N n → suc m ≤N suc n

record CompleteOrderedField
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR inverseR absoluteValueR : R → R
    lessOrEqualR : R → R → Set r
    fromNatR : Nat → R

    oneR-not-zeroR :
      NotEqual oneR zeroR

    addR-commutative :
      (x y : R) →
      addR x y ≡ addR y x
    addR-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    addR-zero :
      (x : R) →
      addR x zeroR ≡ x
    addR-inverse :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiplyR-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiplyR-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) →
      multiplyR x oneR ≡ x
    multiplyR-zero :
      (x : R) →
      multiplyR x zeroR ≡ zeroR
    distributeR :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    multiplyR-inverse :
      (x : R) →
      NotEqual x zeroR →
      multiplyR x (inverseR x) ≡ oneR
    inverseR-zero :
      inverseR zeroR ≡ zeroR

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
    addR-order :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      Both
        (lessOrEqualR zeroR oneR)
        (NotEqual zeroR oneR)

    absoluteR-nonnegative :
      (x : R) →
      lessOrEqualR zeroR (absoluteValueR x)
    absoluteR-of-nonnegative :
      (x : R) →
      lessOrEqualR zeroR x →
      absoluteValueR x ≡ x
    absoluteR-of-nonpositive :
      (x : R) →
      lessOrEqualR x zeroR →
      absoluteValueR x ≡ negateR x

    fromNatR-zero :
      fromNatR zero ≡ zeroR
    fromNatR-successor :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR
    fromNatR-injective :
      (m n : Nat) →
      fromNatR m ≡ fromNatR n →
      m ≡ n

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R → Set r) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqualR x upper) →
      Exists R
        (λ supremum →
          Both
            ((x : R) →
              P x →
              lessOrEqualR x supremum)
            ((upper : R) →
              ((x : R) →
                P x →
                lessOrEqualR x upper) →
              lessOrEqualR supremum upper))

subtractR :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R →
  R →
  R
subtractR reals x y =
  CompleteOrderedField.addR reals
    x
    (CompleteOrderedField.negateR reals y)

divideR :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R →
  R →
  R
divideR reals x y =
  CompleteOrderedField.multiplyR reals
    x
    (CompleteOrderedField.inverseR reals y)

powerR :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R →
  Nat →
  R
powerR reals x zero =
  CompleteOrderedField.oneR reals
powerR reals x (suc n) =
  CompleteOrderedField.multiplyR reals
    (powerR reals x n)
    x

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

partialSumR :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  (Nat → R) →
  Nat →
  R
partialSumR reals term zero =
  CompleteOrderedField.zeroR reals
partialSumR reals term (suc n) =
  CompleteOrderedField.addR reals
    (partialSumR reals term n)
    (term n)

StrictLess :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R →
  R →
  Set r
StrictLess reals x y =
  Both
    (CompleteOrderedField.lessOrEqualR reals x y)
    (NotEqual x y)

Positive :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R →
  Set r
Positive reals x =
  StrictLess reals
    (CompleteOrderedField.zeroR reals)
    x

SequentialLimit :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set r
SequentialLimit reals sequence limit =
  (epsilon : _) →
  Positive reals epsilon →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤N n →
      StrictLess reals
        (CompleteOrderedField.absoluteValueR reals
          (subtractR reals (sequence n) limit))
        epsilon)

exponentialPartialSum :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R →
  Nat →
  R
exponentialPartialSum reals x n =
  partialSumR reals
    (λ k →
      divideR reals
        (powerR reals x k)
        (CompleteOrderedField.fromNatR reals (factorial k)))
    n

alternatingSign :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  Nat →
  R
alternatingSign reals zero =
  CompleteOrderedField.oneR reals
alternatingSign reals (suc n) =
  CompleteOrderedField.negateR reals (alternatingSign reals n)

double : Nat → Nat
double zero = zero
double (suc n) = suc (suc (double n))

oddIndex : Nat → Nat
oddIndex n = suc (double n)

sinePartialSum :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R →
  Nat →
  R
sinePartialSum reals x n =
  partialSumR reals
    (λ k →
      divideR reals
        (CompleteOrderedField.multiplyR reals
          (alternatingSign reals k)
          (powerR reals x (oddIndex k)))
        (CompleteOrderedField.fromNatR reals
          (factorial (oddIndex k))))
    n

record StandardRealAnalysis
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    algebra : CompleteOrderedField R
    squareRoot exponential sine : R → R
    pi : R

    squareRoot-nonnegative :
      (x : R) →
      CompleteOrderedField.lessOrEqualR algebra
        (CompleteOrderedField.zeroR algebra)
        (squareRoot x)
    squareRoot-square :
      (x : R) →
      CompleteOrderedField.lessOrEqualR algebra
        (CompleteOrderedField.zeroR algebra)
        x →
      CompleteOrderedField.multiplyR algebra
        (squareRoot x)
        (squareRoot x) ≡ x
    squareRoot-of-nonpositive :
      (x : R) →
      CompleteOrderedField.lessOrEqualR algebra
        x
        (CompleteOrderedField.zeroR algebra) →
      squareRoot x ≡ CompleteOrderedField.zeroR algebra

    exponential-series :
      (x : R) →
      SequentialLimit algebra
        (exponentialPartialSum algebra x)
        (exponential x)

    sine-series :
      (x : R) →
      SequentialLimit algebra
        (sinePartialSum algebra x)
        (sine x)
    pi-positive :
      Positive algebra pi
    sine-pi :
      sine pi ≡ CompleteOrderedField.zeroR algebra
    sine-positive-before-pi :
      (x : R) →
      Positive algebra x →
      StrictLess algebra x pi →
      Positive algebra (sine x)

two : Nat
two = suc (suc zero)

factorialValue :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  Nat →
  R
factorialValue reals n =
  CompleteOrderedField.fromNatR reals (factorial n)

stirlingApproximation :
  {r : Level} →
  {R : Set r} →
  StandardRealAnalysis R →
  Nat →
  R
stirlingApproximation analysis n =
  CompleteOrderedField.multiplyR reals
    (StandardRealAnalysis.squareRoot analysis
      (CompleteOrderedField.multiplyR reals
        (CompleteOrderedField.multiplyR reals
          (CompleteOrderedField.fromNatR reals two)
          (StandardRealAnalysis.pi analysis))
        (CompleteOrderedField.fromNatR reals n)))
    (powerR reals
      (divideR reals
        (CompleteOrderedField.fromNatR reals n)
        (StandardRealAnalysis.exponential analysis
          (CompleteOrderedField.oneR reals)))
      n)
  where
    reals = StandardRealAnalysis.algebra analysis

AsymptoticallyEquivalent :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  (Nat → R) →
  (Nat → R) →
  Set r
AsymptoticallyEquivalent reals sequence comparison =
  SequentialLimit reals
    (λ n → divideR reals (sequence n) (comparison n))
    (CompleteOrderedField.oneR reals)

stirlings-formula :
  {r : Level} →
  Set (lsuc r)
stirlings-formula {r} =
  (R : Set r) →
  (analysis : StandardRealAnalysis R) →
  AsymptoticallyEquivalent
    (StandardRealAnalysis.algebra analysis)
    (factorialValue (StandardRealAnalysis.algebra analysis))
    (stirlingApproximation analysis)
