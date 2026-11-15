-- Statement-only formalization of miniF2F test problem mathd_algebra_275. This file contains no
-- proof.

module mathd-algebra-275 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record RealExponentialStructure (R : Set) : Set₁ where
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

    exponential-zero :
      exponential zeroR ≡ oneR
    exponential-add :
      (x y : R) →
      exponential (add x y) ≡
      multiply (exponential x) (exponential y)
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

subtract :
  {R : Set} →
  RealExponentialStructure R →
  R →
  R →
  R
subtract reals x y =
  RealExponentialStructure.add reals x
    (RealExponentialStructure.negate reals y)

divide :
  {R : Set} →
  RealExponentialStructure R →
  R →
  R →
  R
divide reals x y =
  RealExponentialStructure.multiply reals x
    (RealExponentialStructure.inverse reals y)

realPower :
  {R : Set} →
  RealExponentialStructure R →
  R →
  R →
  R
realPower reals base exponent =
  RealExponentialStructure.exponential reals
    (RealExponentialStructure.multiply reals exponent
      (RealExponentialStructure.logarithm reals base))

fourthRootOfEleven :
  {R : Set} →
  RealExponentialStructure R →
  R
fourthRootOfEleven reals =
  realPower reals
    (RealExponentialStructure.fromNat reals 11)
    (divide reals
      (RealExponentialStructure.fromNat reals 1)
      (RealExponentialStructure.fromNat reals 4))

mathd-algebra-275 : Set₁
mathd-algebra-275 =
  (R : Set) →
  (reals : RealExponentialStructure R) →
  (x : R) →
  realPower reals
    (fourthRootOfEleven reals)
    (subtract reals
      (RealExponentialStructure.multiply reals
        (RealExponentialStructure.fromNat reals 3)
        x)
      (RealExponentialStructure.fromNat reals 3))
    ≡ divide reals
        (RealExponentialStructure.fromNat reals 1)
        (RealExponentialStructure.fromNat reals 5) →
  realPower reals
    (fourthRootOfEleven reals)
    (RealExponentialStructure.add reals
      (RealExponentialStructure.multiply reals
        (RealExponentialStructure.fromNat reals 6)
        x)
      (RealExponentialStructure.fromNat reals 2))
    ≡ divide reals
        (RealExponentialStructure.fromNat reals 121)
        (RealExponentialStructure.fromNat reals 25)
