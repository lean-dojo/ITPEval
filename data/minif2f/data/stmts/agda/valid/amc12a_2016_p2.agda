-- Statement-only formalization of miniF2F valid problem amc12a_2016_p2:
-- a real-exponent equation with positive integer bases determines x = 3.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module amc12a-2016-p2 where

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

AtMost : {A : Set} → (A → A → Set) → A → A → Set
AtMost relation x y = relation x y ∨ x ≡ y

-- Complete Archimedean ordered fields are categorical for the real numbers.
-- The monotone exponential and its positive-domain inverse give the standard
-- real-power operation used by the Lean source.
record StandardReal (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse exponential logarithm : R → R
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

    order-irreflexive :
      (x : R) → lessThan x x → ⊥
    order-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-order :
      (x y z : R) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      lessThan zeroR (multiply x y)
    zero-less-than-one :
      lessThan zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-positive :
      (n : Nat) → lessThan zeroR (fromNat (suc n))

    archimedean :
      (x : R) →
      Exists Nat λ n →
        AtMost lessThan x (fromNat n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          AtMost lessThan x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          AtMost lessThan x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            AtMost lessThan x upper) →
          AtMost lessThan supremum upper)

    exponential-zero :
      exponential zeroR ≡ oneR
    exponential-add :
      (x y : R) →
      exponential (add x y) ≡
      multiply (exponential x) (exponential y)
    exponential-order :
      (x y : R) →
      lessThan x y →
      lessThan (exponential x) (exponential y)
    exponential-positive :
      (x : R) → lessThan zeroR (exponential x)
    logarithm-zero :
      logarithm zeroR ≡ zeroR
    logarithm-one :
      logarithm oneR ≡ zeroR
    exponential-logarithm :
      (x : R) →
      lessThan zeroR x →
      exponential (logarithm x) ≡ x
    logarithm-exponential :
      (x : R) → logarithm (exponential x) ≡ x

naturalPower :
  {R : Set} →
  StandardReal R →
  R →
  Nat →
  R
naturalPower reals x zero =
  StandardReal.oneR reals
naturalPower reals x (suc n) =
  StandardReal.multiply reals x (naturalPower reals x n)

realPower :
  {R : Set} →
  StandardReal R →
  R →
  R →
  R
realPower reals base exponent =
  StandardReal.exponential reals
    (StandardReal.multiply reals exponent
      (StandardReal.logarithm reals base))

amc12a-2016-p2 : Set₁
amc12a-2016-p2 =
  (R : Set) →
  (reals : StandardReal R) →
  (x : R) →
  StandardReal.multiply reals
    (realPower reals
      (StandardReal.fromNat reals 10)
      x)
    (realPower reals
      (StandardReal.fromNat reals 100)
      (StandardReal.multiply reals
        (StandardReal.fromNat reals 2)
        x))
  ≡
  naturalPower reals
    (StandardReal.fromNat reals 1000)
    5 →
  x ≡ StandardReal.fromNat reals 3
