-- Statement-only formalization of miniF2F valid problem mathd_algebra_482:
-- over the real numbers, two distinct prime natural roots of x^2 - 12*x + k
-- force k = 35. This file contains no proof.

module mathd-algebra-482 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≠_ _≤_ _∣_
infixr 3 _∨_
infixr 2 _∧_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

record OrderedField (R : Set) : Set₁ where
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

-- Complete Archimedean ordered fields characterize the standard real-number
-- domain up to the unique ordered-field isomorphism.
record StandardReals (R : Set) : Set₁ where
  field
    algebra : OrderedField R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        OrderedField.lessOrEqual algebra
          x
          (OrderedField.fromNat algebra n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          OrderedField.lessOrEqual algebra x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          OrderedField.lessOrEqual algebra x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            OrderedField.lessOrEqual algebra x upper) →
          OrderedField.lessOrEqual algebra supremum upper)

polynomial :
  {R : Set} →
  OrderedField R →
  R →
  R →
  R
polynomial reals k x =
  OrderedField.add reals
    (OrderedField.add reals
      (OrderedField.multiply reals x x)
      (OrderedField.negate reals
        (OrderedField.multiply reals
          (OrderedField.fromNat reals 12)
          x)))
    k

mathd-algebra-482 : Set₁
mathd-algebra-482 =
  (R : Set) →
  (standard : StandardReals R) →
  (m n : Nat) →
  (k : R) →
  (f : R → R) →
  Prime m →
  Prime n →
  ((x : R) →
    f x ≡ polynomial (StandardReals.algebra standard) k x) →
  f (OrderedField.fromNat (StandardReals.algebra standard) m) ≡
    OrderedField.zeroR (StandardReals.algebra standard) →
  f (OrderedField.fromNat (StandardReals.algebra standard) n) ≡
    OrderedField.zeroR (StandardReals.algebra standard) →
  m ≠ n →
  k ≡ OrderedField.fromNat (StandardReals.algebra standard) 35
