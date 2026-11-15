-- Statement-only formalization of miniF2F valid problem
-- algebra_amgm_sumasqdivbsqgeqsumbdiva: a cyclic inequality for three
-- positive real numbers involving sums of squared ratios. This file contains no proof.

module algebra_amgm_sumasqdivbsqgeqsumbdiva where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record RealStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
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

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

strictlyPositive : {R : Set} → RealStructure R → R → Set
strictlyPositive reals x =
  (RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals) x) ∧
  (RealStructure.zeroR reals ≠ x)

sumThree :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R →
  R
sumThree reals x y z =
  RealStructure.add reals
    (RealStructure.add reals x y)
    z

squareRatioSum :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R →
  R
squareRatioSum reals a b c =
  sumThree reals
    (divide reals (square reals a) (square reals b))
    (divide reals (square reals b) (square reals c))
    (divide reals (square reals c) (square reals a))

ratioSum :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R →
  R
ratioSum reals a b c =
  sumThree reals
    (divide reals b a)
    (divide reals c b)
    (divide reals a c)

module Statement {R : Set} (standard : StandardReal R) where
  reals : RealStructure R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (a b c : R) →
    (strictlyPositive reals a ∧
     strictlyPositive reals b ∧
     strictlyPositive reals c) →
    RealStructure.lessOrEqual reals
      (ratioSum reals a b c)
      (squareRatioSum reals a b c)

algebra_amgm_sumasqdivbsqgeqsumbdiva : Set₁
algebra_amgm_sumasqdivbsqgeqsumbdiva =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
