-- Statement-only formalization of miniF2F valid problem
-- algebra_binomnegdiscrineq_10alt28asqp1: the real quadratic inequality
-- 10 * a <= 28 * a^2 + 1 for every real a. This file contains no proof.
-- Real numbers are represented by a bundled complete Archimedean ordered
-- field, which characterizes ℝ up to ordered-field isomorphism; the displayed
-- inequality is invariant under that isomorphism.

module algebra_binomnegdiscrineq_10alt28asqp1 where

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
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record CompleteArchimedeanOrderedField (R : Set) : Set₁ where
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

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) → P x → lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

record RealNumbers : Set₁ where
  field
    Carrier : Set
    structure : CompleteArchimedeanOrderedField Carrier

Real : RealNumbers → Set
Real = RealNumbers.Carrier

realStructure :
  (reals : RealNumbers) →
  CompleteArchimedeanOrderedField (Real reals)
realStructure = RealNumbers.structure

square : (reals : RealNumbers) → Real reals → Real reals
square reals x =
  CompleteArchimedeanOrderedField.multiply (realStructure reals) x x

algebra_binomnegdiscrineq_10alt28asqp1 : Set₁
algebra_binomnegdiscrineq_10alt28asqp1 =
  (reals : RealNumbers) →
  (a : Real reals) →
  CompleteArchimedeanOrderedField.lessOrEqual (realStructure reals)
    (CompleteArchimedeanOrderedField.multiply (realStructure reals)
      (CompleteArchimedeanOrderedField.fromNat (realStructure reals) 10)
      a)
    (CompleteArchimedeanOrderedField.add (realStructure reals)
      (CompleteArchimedeanOrderedField.multiply (realStructure reals)
        (CompleteArchimedeanOrderedField.fromNat (realStructure reals) 28)
        (square reals a))
      (CompleteArchimedeanOrderedField.fromNat (realStructure reals) 1))
