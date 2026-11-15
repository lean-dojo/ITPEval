-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__091, "The Triangle Inequality": in every real
-- inner-product space, the norm of x + y is at most the sum of the two norms.
-- This file contains no proof.

module TriangleInequality where

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
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

-- Complete Archimedean ordered fields present the standard real numbers
-- up to ordered-field isomorphism.
record CompleteArchimedeanOrderedField (R : Set) : Set₁ where
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

    absolute-nonnegative :
      (x : R) → lessOrEqual zeroR (absoluteValue x)
    absolute-of-nonnegative :
      (x : R) →
      lessOrEqual zeroR x →
      absoluteValue x ≡ x
    absolute-of-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      absoluteValue x ≡ negate x

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
      Σ R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

record RealInnerProductSpace
  (R : Set)
  (reals : CompleteArchimedeanOrderedField R)
  (V : Set) : Set₁ where
  open CompleteArchimedeanOrderedField reals

  field
    zeroV : V
    addV : V → V → V
    negateV : V → V
    scaleV : R → V → V
    inner : V → V → R

    addV-commutative :
      (x y : V) →
      addV x y ≡ addV y x
    addV-associative :
      (x y z : V) →
      addV (addV x y) z ≡ addV x (addV y z)
    addV-zero :
      (x : V) →
      addV x zeroV ≡ x
    addV-inverse :
      (x : V) →
      addV x (negateV x) ≡ zeroV

    scaleV-one :
      (x : V) →
      scaleV oneR x ≡ x
    scaleV-associative :
      (a b : R) →
      (x : V) →
      scaleV (multiply a b) x ≡ scaleV a (scaleV b x)
    scaleV-add-scalars :
      (a b : R) →
      (x : V) →
      scaleV (add a b) x ≡ addV (scaleV a x) (scaleV b x)
    scaleV-add-vectors :
      (a : R) →
      (x y : V) →
      scaleV a (addV x y) ≡ addV (scaleV a x) (scaleV a y)

    inner-symmetric :
      (x y : V) →
      inner x y ≡ inner y x
    inner-add-left :
      (x y z : V) →
      inner (addV x y) z ≡ add (inner x z) (inner y z)
    inner-scale-left :
      (a : R) →
      (x y : V) →
      inner (scaleV a x) y ≡ multiply a (inner x y)
    inner-nonnegative :
      (x : V) →
      lessOrEqual zeroR (inner x x)
    inner-definite :
      (x : V) →
      inner x x ≡ zeroR →
      x ≡ zeroV

the-triangle-inequality : Set₁
the-triangle-inequality =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (V : Set) →
  (space : RealInnerProductSpace R reals V) →
  (x y : V) →
  (norm-x norm-y norm-sum : R) →
  let open CompleteArchimedeanOrderedField reals
      open RealInnerProductSpace space
  in
  lessOrEqual zeroR norm-x →
  lessOrEqual zeroR norm-y →
  lessOrEqual zeroR norm-sum →
  multiply norm-x norm-x ≡ inner x x →
  multiply norm-y norm-y ≡ inner y y →
  multiply norm-sum norm-sum ≡ inner (addV x y) (addV x y) →
  lessOrEqual norm-sum (add norm-x norm-y)
