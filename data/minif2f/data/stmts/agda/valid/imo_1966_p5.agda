-- Statement-only formalization of miniF2F valid problem imo_1966_p5: four
-- distance-weighted equations for strictly decreasing real values determine
-- the two endpoint coefficients. This file contains no proof.

module imo-1966-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record RealStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse absoluteValue : R → R
    lessOrEqual : R → R → Set
    fromNat : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → add x y ≡ add y x
    add-associative :
      (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : R) → add x zeroR ≡ x
    add-inverse :
      (x : R) → add x (negate x) ≡ zeroR

    multiply-commutative :
      (x y : R) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : R) → multiply x oneR ≡ x
    multiply-zero :
      (x : R) → multiply x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR

    order-reflexive :
      (x : R) → lessOrEqual x x
    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y
    order-total :
      (x y : R) → lessOrEqual x y ∨ lessOrEqual y x
    add-monotone :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-or-equal-one :
      lessOrEqual zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

    absolute-value-nonnegative :
      (x : R) → lessOrEqual zeroR (absoluteValue x)
    absolute-value-of-nonnegative :
      (x : R) →
      lessOrEqual zeroR x →
      absoluteValue x ≡ x
    absolute-value-of-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      absoluteValue x ≡ negate x

-- Archimedean completeness characterizes the standard real-number domain.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : RealStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        RealStructure.lessOrEqual arithmetic
          x
          (RealStructure.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealStructure.lessOrEqual arithmetic x upper) →
          RealStructure.lessOrEqual arithmetic supremum upper)

subtract :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R
subtract reals x y =
  RealStructure.add reals x
    (RealStructure.negate reals y)

divide :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R
divide reals x y =
  RealStructure.multiply reals x
    (RealStructure.inverse reals y)

strictlyLess :
  {R : Set} →
  RealStructure R →
  R →
  R →
  Set
strictlyLess reals x y =
  RealStructure.lessOrEqual reals x y ∧ x ≠ y

distance :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R
distance reals x y =
  RealStructure.absoluteValue reals
    (subtract reals x y)

weightedTerm :
  {R : Set} →
  RealStructure R →
  (Nat → R) →
  (Nat → R) →
  Nat →
  Nat →
  R
weightedTerm reals a x i j =
  RealStructure.multiply reals
    (distance reals (a i) (a j))
    (x j)

rowEquation :
  {R : Set} →
  RealStructure R →
  (Nat → R) →
  (Nat → R) →
  Nat →
  Nat →
  Nat →
  Nat →
  Set
rowEquation reals a x i j k l =
  RealStructure.add reals
    (RealStructure.add reals
      (weightedTerm reals a x i j)
      (weightedTerm reals a x i k))
    (weightedTerm reals a x i l)
  ≡ RealStructure.oneR reals

endpointValue :
  {R : Set} →
  RealStructure R →
  (Nat → R) →
  R
endpointValue reals a =
  divide reals
    (RealStructure.oneR reals)
    (distance reals (a 1) (a 4))

module Statement {R : Set} (standard : StandardReal R) where
  reals : RealStructure R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (x a : Nat → R) →
    a 1 ≠ a 2 →
    a 1 ≠ a 3 →
    a 1 ≠ a 4 →
    a 2 ≠ a 3 →
    a 2 ≠ a 4 →
    a 3 ≠ a 4 →
    strictlyLess reals (a 2) (a 1) →
    strictlyLess reals (a 3) (a 2) →
    strictlyLess reals (a 4) (a 3) →
    rowEquation reals a x 1 2 3 4 →
    rowEquation reals a x 2 1 3 4 →
    rowEquation reals a x 3 1 2 4 →
    rowEquation reals a x 4 1 2 3 →
    x 2 ≡ RealStructure.zeroR reals ∧
    x 3 ≡ RealStructure.zeroR reals ∧
    x 1 ≡ endpointValue reals a ∧
    x 4 ≡ endpointValue reals a

imo-1966-p5 : Set₁
imo-1966-p5 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
