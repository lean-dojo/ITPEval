-- Statement-only formalization of miniF2F test problem mathd_algebra_246:
-- a real quartic function of the displayed form with value 2 at -3 has
-- value 8 at 3. This file contains no proof.

module mathd-algebra-246 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_

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
      (x y : R) →
      lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR ∧ oneR ≠ zeroR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    archimedean :
      (x : R) → Σ Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Σ R (λ x → P x) →
      Σ R (λ upper → (x : R) → P x → lessOrEqual x upper) →
      Σ R (λ supremum →
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

subtract :
  (reals : RealNumbers) →
  Real reals →
  Real reals →
  Real reals
subtract reals x y =
  CompleteArchimedeanOrderedField.add (realStructure reals) x
    (CompleteArchimedeanOrderedField.negate (realStructure reals) y)

naturalPower :
  (reals : RealNumbers) →
  Real reals →
  Nat →
  Real reals
naturalPower reals x zero =
  CompleteArchimedeanOrderedField.oneR (realStructure reals)
naturalPower reals x (suc n) =
  CompleteArchimedeanOrderedField.multiply (realStructure reals) x
    (naturalPower reals x n)

mathd-algebra-246 : Set₁
mathd-algebra-246 =
  (reals : RealNumbers) →
  (a b : Real reals) →
  (f : Real reals → Real reals) →
  ((x : Real reals) →
    f x ≡
    CompleteArchimedeanOrderedField.add (realStructure reals)
      (CompleteArchimedeanOrderedField.add (realStructure reals)
        (subtract reals
          (CompleteArchimedeanOrderedField.multiply
            (realStructure reals) a
            (naturalPower reals x 4))
          (CompleteArchimedeanOrderedField.multiply
            (realStructure reals) b
            (naturalPower reals x 2)))
        x)
      (CompleteArchimedeanOrderedField.fromNat
        (realStructure reals) 5)) →
  f (CompleteArchimedeanOrderedField.negate (realStructure reals)
      (CompleteArchimedeanOrderedField.fromNat
        (realStructure reals) 3))
    ≡ CompleteArchimedeanOrderedField.fromNat
        (realStructure reals) 2 →
  f (CompleteArchimedeanOrderedField.fromNat
      (realStructure reals) 3)
    ≡ CompleteArchimedeanOrderedField.fromNat
        (realStructure reals) 8
