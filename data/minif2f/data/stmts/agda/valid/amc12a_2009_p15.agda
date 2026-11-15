-- Statement-only formalization of miniF2F valid problem amc12a_2009_p15: a positive natural
-- determined by a finite complex sum of k times i to the kth power. This file contains no proof.

module amc12a-2009-p15 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ _≠_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data _<_ : Nat → Nat → Set where
  zero<suc : {n : Nat} → zero < suc n
  suc<suc  : {m n : Nat} → m < n → suc m < suc n

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

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

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

record Complex (R : Set) : Set where
  constructor mkComplex
  field
    real      : R
    imaginary : R

complexAdd :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (CompleteArchimedeanOrderedField.add reals a c)
    (CompleteArchimedeanOrderedField.add reals b d)

complexMultiply :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (CompleteArchimedeanOrderedField.add reals
      (CompleteArchimedeanOrderedField.multiply reals a c)
      (CompleteArchimedeanOrderedField.negate reals
        (CompleteArchimedeanOrderedField.multiply reals b d)))
    (CompleteArchimedeanOrderedField.add reals
      (CompleteArchimedeanOrderedField.multiply reals a d)
      (CompleteArchimedeanOrderedField.multiply reals b c))

complexFromNat :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Nat →
  Complex R
complexFromNat reals n =
  mkComplex
    (CompleteArchimedeanOrderedField.fromNat reals n)
    (CompleteArchimedeanOrderedField.zeroR reals)

complexI :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Complex R
complexI reals =
  mkComplex
    (CompleteArchimedeanOrderedField.zeroR reals)
    (CompleteArchimedeanOrderedField.oneR reals)

complexPower :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Complex R →
  Nat →
  Complex R
complexPower reals z zero =
  complexFromNat reals 1
complexPower reals z (suc n) =
  complexMultiply reals z (complexPower reals z n)

summand :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Nat →
  Complex R
summand reals k =
  complexMultiply reals
    (complexFromNat reals k)
    (complexPower reals (complexI reals) k)

sumFromOne :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Nat →
  Complex R
sumFromOne reals zero =
  complexFromNat reals 0
sumFromOne reals (suc n) =
  complexAdd reals
    (sumFromOne reals n)
    (summand reals (suc n))

amc12a-2009-p15 : Set₁
amc12a-2009-p15 =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (n : Nat) →
  zero < n →
  sumFromOne reals n
    ≡
    complexAdd reals
      (complexFromNat reals 48)
      (complexMultiply reals
        (complexFromNat reals 49)
        (complexI reals)) →
  n ≡ 97
