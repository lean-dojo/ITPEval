-- Statement-only formalization of miniF2F test problem
-- induction_pord1p1on2powklt5on2: a strict upper bound for the finite real
-- product of 1 + 1 / 2^k over k from 1 through a positive n. This file
-- contains no proof.

module induction_pord1p1on2powklt5on2 where

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

data NatLess : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} → NatLess zero (suc n)
  successor-less-successor :
    {m n : Nat} → NatLess m n → NatLess (suc m) (suc n)

PositiveNat : Nat → Set
PositiveNat n = NatLess zero n

record CompleteArchimedeanOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessThan : R → R → Set
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

    less-irreflexive :
      (x : R) → lessThan x x → ⊥
    less-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-strict-monotone :
      (x y z : R) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      lessThan zeroR (multiply x y)
    zero-less-one :
      lessThan zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessThan x (fromNat n))

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessThan x upper ∨ x ≡ upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            subset x →
            lessThan x supremum ∨ x ≡ supremum) ∧
          ((upper : R) →
            ((x : R) →
              subset x →
              lessThan x upper ∨ x ≡ upper) →
            lessThan supremum upper ∨ supremum ≡ upper))

divide : {R : Set} → CompleteArchimedeanOrderedField R → R → R → R
divide reals x y =
  CompleteArchimedeanOrderedField.multiply reals x
    (CompleteArchimedeanOrderedField.inverse reals y)

power : {R : Set} → CompleteArchimedeanOrderedField R → R → Nat → R
power reals x zero =
  CompleteArchimedeanOrderedField.oneR reals
power reals x (suc n) =
  CompleteArchimedeanOrderedField.multiply reals x (power reals x n)

factor :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Nat →
  R
factor reals k =
  CompleteArchimedeanOrderedField.add reals
    (CompleteArchimedeanOrderedField.oneR reals)
    (divide reals
      (CompleteArchimedeanOrderedField.oneR reals)
      (power reals
        (CompleteArchimedeanOrderedField.fromNat reals 2)
        k))

productOneTo :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Nat →
  R
productOneTo reals zero =
  CompleteArchimedeanOrderedField.oneR reals
productOneTo reals (suc n) =
  CompleteArchimedeanOrderedField.multiply reals
    (productOneTo reals n)
    (factor reals (suc n))

induction_pord1p1on2powklt5on2 : Set₁
induction_pord1p1on2powklt5on2 =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (n : Nat) →
  PositiveNat n →
  CompleteArchimedeanOrderedField.lessThan reals
    (productOneTo reals n)
    (divide reals
      (CompleteArchimedeanOrderedField.fromNat reals 5)
      (CompleteArchimedeanOrderedField.fromNat reals 2))
