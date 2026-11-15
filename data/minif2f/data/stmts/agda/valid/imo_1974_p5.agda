-- Statement-only formalization of miniF2F valid problem imo_1974_p5: the cyclic fractional
-- sum of four positive real numbers lies strictly between one and two. This file contains
-- no proof.

module imo-1974-p5 where

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

record LinearOrderedField (R : Set) : Set₁ where
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

-- Archimedean completeness characterizes the standard real-number domain.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : LinearOrderedField R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        LinearOrderedField.lessThan arithmetic
          x
          (LinearOrderedField.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          LinearOrderedField.lessThan arithmetic x upper ∨ x ≡ upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          LinearOrderedField.lessThan arithmetic x supremum ∨
          x ≡ supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            LinearOrderedField.lessThan arithmetic x upper ∨
            x ≡ upper) →
          LinearOrderedField.lessThan arithmetic supremum upper ∨
          supremum ≡ upper)

module Statement {R : Set} (standard : StandardReal R) where
  reals : LinearOrderedField R
  reals = StandardReal.arithmetic standard

  open LinearOrderedField reals

  infixl 6 _+_
  infixl 7 _*_ _/_
  infix 4 _<_

  _+_ : R → R → R
  _+_ = add

  _*_ : R → R → R
  _*_ = multiply

  _/_ : R → R → R
  x / y = x * inverse y

  _<_ : R → R → Set
  _<_ = lessThan

  two : R
  two = oneR + oneR

  fractionSum : R → R → R → R → R
  fractionSum a b c d =
    a / ((a + b) + d) +
    b / ((a + b) + c) +
    c / ((b + c) + d) +
    d / ((a + c) + d)

  proposition : Set
  proposition =
    (a b c d s : R) →
    zeroR < a →
    zeroR < b →
    zeroR < c →
    zeroR < d →
    s ≡ fractionSum a b c d →
    (oneR < s) ∧ (s < two)

imo-1974-p5 : Set₁
imo-1974-p5 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
