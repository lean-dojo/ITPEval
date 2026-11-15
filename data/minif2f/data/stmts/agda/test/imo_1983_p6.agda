-- Statement-only formalization of miniF2F test problem imo_1983_p6: a cyclic
-- quartic inequality for positive real triangle side lengths. This file contains no proof.

module imo-1983-p6 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data ⊥ : Set where

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

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

record LinearOrderedField (F : Set) : Set₁ where
  field
    zeroF oneF : F
    add multiply : F → F → F
    negate inverse : F → F
    lessThan : F → F → Set
    fromNat : Nat → F

    one-not-zero :
      oneF ≠ zeroF

    add-commutative :
      (x y : F) → add x y ≡ add y x
    add-associative :
      (x y z : F) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : F) → add x zeroF ≡ x
    add-inverse :
      (x : F) → add x (negate x) ≡ zeroF

    multiply-commutative :
      (x y : F) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : F) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : F) → multiply x oneF ≡ x
    multiply-zero :
      (x : F) → multiply x zeroF ≡ zeroF
    distribute :
      (x y z : F) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroF ≡ zeroF
    multiply-inverse :
      (x : F) →
      x ≠ zeroF →
      multiply x (inverse x) ≡ oneF

    order-irreflexive :
      (x : F) → lessThan x x → ⊥
    order-transitive :
      (x y z : F) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : F) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-order :
      (x y z : F) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : F) →
      lessThan zeroF x →
      lessThan zeroF y →
      lessThan zeroF (multiply x y)
    zero-less-than-one :
      lessThan zeroF oneF

    fromNat-zero :
      fromNat zero ≡ zeroF
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneF
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

lessOrEqual :
  {R : Set} →
  LinearOrderedField R →
  R →
  R →
  Set
lessOrEqual reals x y =
  LinearOrderedField.lessThan reals x y ∨ x ≡ y

-- Archimedean completeness characterizes the standard real-number domain.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : LinearOrderedField R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        lessOrEqual arithmetic x
          (LinearOrderedField.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            lessOrEqual arithmetic x upper) →
          lessOrEqual arithmetic supremum upper)

module Statement {R : Set} (standard : StandardReal R) where
  reals : LinearOrderedField R
  reals = StandardReal.arithmetic standard

  open LinearOrderedField reals

  infixl 6 _+_ _-_
  infixl 7 _*_
  infix 4 _<_ _≤_

  _+_ : R → R → R
  _+_ = add

  _-_ : R → R → R
  x - y = x + negate y

  _*_ : R → R → R
  _*_ = multiply

  _<_ : R → R → Set
  _<_ = lessThan

  _≤_ : R → R → Set
  _≤_ = lessOrEqual reals

  square : R → R
  square x = x * x

  proposition : Set
  proposition =
    (a b c : R) →
    zeroF < a →
    zeroF < b →
    zeroF < c →
    c < a + b →
    b < a + c →
    a < b + c →
    zeroF ≤
      square a * b * (a - b) +
      square b * c * (b - c) +
      square c * a * (c - a)

imo-1983-p6 : Set₁
imo-1983-p6 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
