-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__088, "Derangements Formula": the number of
-- fixed-point-free permutations of a nonempty finite set is round(n! / e).
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

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to : A → B
    from : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

record Derangement
  {a : Level}
  (A : Set a) :
  Set a where

  field
    permutation : Bijection A A
    fixed-point-free :
      (x : A) →
      NotEqual (Bijection.to permutation x) x

SameDerangement :
  {a : Level} →
  {A : Set a} →
  Derangement A →
  Derangement A →
  Set a
SameDerangement {A = A} left-derangement right-derangement =
  (x : A) →
  Bijection.to (Derangement.permutation left-derangement) x ≡
  Bijection.to (Derangement.permutation right-derangement) x

record HasExtensionalCardinality
  {a e : Level}
  {A : Set a}
  (equivalent : A → A → Set e)
  (cardinality : Nat) :
  Set (a ⊔ e) where

  field
    enumerate :
      Fin cardinality →
      A

    enumeration-complete :
      (item : A) →
      Exists (Fin cardinality)
        (λ index → equivalent item (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) →
      equivalent (enumerate left-index) (enumerate right-index) →
      left-index ≡ right-index

DerangementFamily :
  {a : Level} →
  (A : Set a) →
  Nat →
  Set a
DerangementFamily A cardinality =
  HasExtensionalCardinality
    {A = Derangement A}
    SameDerangement
    cardinality

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

record StandardRealAnalysis
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    algebra : CompleteOrderedField R
    exponential : R → R
    exponential-series :
      (x : R) →
      SequentialLimit algebra
        (exponentialPartialSum algebra x)
        (exponential x)

two : Nat
two = suc (suc zero)

half :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  R
half reals =
  CompleteOrderedField.inverseR reals
    (CompleteOrderedField.fromNatR reals two)

RoundsTo :
  {r : Level} →
  {R : Set r} →
  CompleteOrderedField R →
  Nat →
  R →
  Set r
RoundsTo reals integer x =
  Both
    (CompleteOrderedField.lessOrEqualR reals
      (subtractR reals
        (CompleteOrderedField.fromNatR reals integer)
        (half reals))
      x)
    (StrictLess reals
      x
      (CompleteOrderedField.addR reals
        (CompleteOrderedField.fromNatR reals integer)
        (half reals)))

derangements-formula :
  {a r : Level} →
  Set (lsuc (a ⊔ r))
derangements-formula {a} {r} =
  (R : Set r) →
  (analysis : StandardRealAnalysis R) →
  (A : Set a) →
  (n : Nat) →
  NotEqual n zero →
  Bijection A (Fin n) →
  Exists Nat
    (λ count →
      Both
        (DerangementFamily A count)
        (RoundsTo
          (StandardRealAnalysis.algebra analysis)
          count
          (divideR
            (StandardRealAnalysis.algebra analysis)
            (CompleteOrderedField.fromNatR
              (StandardRealAnalysis.algebra analysis)
              (factorial n))
            (StandardRealAnalysis.exponential analysis
              (CompleteOrderedField.oneR
                (StandardRealAnalysis.algebra analysis))))))
