-- Statement-only formalization of miniF2F test problem
-- algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7: a complex linear
-- system implying f = -10 and z = 7. This file contains no proof.

module algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 where

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
-- isomorphism, so this structurally presents the concrete real numbers.
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

complexNegate :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Complex R →
  Complex R
complexNegate reals (mkComplex a b) =
  mkComplex
    (CompleteArchimedeanOrderedField.negate reals a)
    (CompleteArchimedeanOrderedField.negate reals b)

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

complexSubtract :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexSubtract reals x y =
  complexAdd reals x (complexNegate reals y)

complexFromNat :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  Nat →
  Complex R
complexFromNat reals n =
  mkComplex
    (CompleteArchimedeanOrderedField.fromNat reals n)
    (CompleteArchimedeanOrderedField.zeroR reals)

algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 : Set₁
algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (f z : Complex R) →
  complexAdd reals f
      (complexMultiply reals (complexFromNat reals 3) z)
    ≡ complexFromNat reals 11 →
  complexSubtract reals
      (complexMultiply reals
        (complexFromNat reals 3)
        (complexSubtract reals f (complexFromNat reals 1)))
      (complexMultiply reals (complexFromNat reals 5) z)
    ≡ complexNegate reals (complexFromNat reals 68) →
  (f ≡ complexNegate reals (complexFromNat reals 10)) ∧
  (z ≡ complexFromNat reals 7)
