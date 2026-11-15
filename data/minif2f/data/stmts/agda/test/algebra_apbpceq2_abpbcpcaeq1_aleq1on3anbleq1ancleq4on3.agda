-- Statement-only formalization of miniF2F test problem
-- algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3: interval bounds
-- for ordered real numbers with a + b + c = 2 and ab + bc + ca = 1.
-- This file contains no proof.

module algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 where

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

-- Complete Archimedean ordered fields are unique up to ordered-field
-- isomorphism, so this structurally presents the standard real numbers.
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

divide :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R
divide reals x y =
  CompleteArchimedeanOrderedField.multiply reals x
    (CompleteArchimedeanOrderedField.inverse reals y)

sumThree :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R →
  R
sumThree reals x y z =
  CompleteArchimedeanOrderedField.add reals
    (CompleteArchimedeanOrderedField.add reals x y)
    z

pairwiseProductSum :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R →
  R
pairwiseProductSum reals a b c =
  add
    (add (multiply a b) (multiply b c))
    (multiply c a)
  where
    open CompleteArchimedeanOrderedField reals

oneThird :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R
oneThird reals =
  divide reals
    (CompleteArchimedeanOrderedField.fromNat reals 1)
    (CompleteArchimedeanOrderedField.fromNat reals 3)

fourThirds :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R
fourThirds reals =
  divide reals
    (CompleteArchimedeanOrderedField.fromNat reals 4)
    (CompleteArchimedeanOrderedField.fromNat reals 3)

algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 : Set₁
algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (a b c : R) →
  (CompleteArchimedeanOrderedField.lessOrEqual reals a b ∧
   CompleteArchimedeanOrderedField.lessOrEqual reals b c) →
  sumThree reals a b c ≡
    CompleteArchimedeanOrderedField.fromNat reals 2 →
  pairwiseProductSum reals a b c ≡
    CompleteArchimedeanOrderedField.fromNat reals 1 →
  CompleteArchimedeanOrderedField.lessOrEqual reals
    (CompleteArchimedeanOrderedField.zeroR reals) a ∧
  CompleteArchimedeanOrderedField.lessOrEqual reals a (oneThird reals) ∧
  CompleteArchimedeanOrderedField.lessOrEqual reals (oneThird reals) b ∧
  CompleteArchimedeanOrderedField.lessOrEqual reals b
    (CompleteArchimedeanOrderedField.oneR reals) ∧
  CompleteArchimedeanOrderedField.lessOrEqual reals
    (CompleteArchimedeanOrderedField.oneR reals) c ∧
  CompleteArchimedeanOrderedField.lessOrEqual reals c (fourThirds reals)
