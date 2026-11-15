-- Statement-only formalization of miniF2F valid problem
-- algebra_amgm_prod1toneq1_sum1tongeqn: the AM-GM sum bound for nonnegative
-- reals whose first n terms have product 1. This file contains no proof.

module algebra_amgm_prod1toneq1_sum1tongeqn where

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

sumInitial :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  (Nat → R) →
  Nat →
  R
sumInitial reals a zero =
  CompleteArchimedeanOrderedField.zeroR reals
sumInitial reals a (suc n) =
  CompleteArchimedeanOrderedField.add reals
    (sumInitial reals a n)
    (a n)

productInitial :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  (Nat → R) →
  Nat →
  R
productInitial reals a zero =
  CompleteArchimedeanOrderedField.oneR reals
productInitial reals a (suc n) =
  CompleteArchimedeanOrderedField.multiply reals
    (productInitial reals a n)
    (a n)

algebra_amgm_prod1toneq1_sum1tongeqn : Set₁
algebra_amgm_prod1toneq1_sum1tongeqn =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (a : Nat → R) →
  (n : Nat) →
  ((i : Nat) →
    CompleteArchimedeanOrderedField.lessOrEqual reals
      (CompleteArchimedeanOrderedField.zeroR reals)
      (a i)) →
  productInitial reals a n ≡
    CompleteArchimedeanOrderedField.oneR reals →
  CompleteArchimedeanOrderedField.lessOrEqual reals
    (CompleteArchimedeanOrderedField.fromNat reals n)
    (sumInitial reals a n)
