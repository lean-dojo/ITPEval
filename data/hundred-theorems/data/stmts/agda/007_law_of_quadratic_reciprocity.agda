-- Statement-only formalization of "Law of Quadratic Reciprocity" from Hundred Theorems item
-- 007. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _≠_ _∣_
infixr 3 _∨_ _∧_
infix 2 _↔_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ n
  s≤s : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (d n : Nat) : Set where
  field
    quotient : Nat
    division-equation : n ≡ d * quotient

data _∨_ (A B : Set) : Set where
  or-left : A → A ∨ B
  or-right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  field
    first : A
    second : B

record _↔_ (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial : (d : Nat) → d ∣ n → d ≡ 1 ∨ d ≡ n

record Odd (n : Nat) : Set where
  field
    odd-witness : Nat
    odd-equation : n ≡ 2 * odd-witness + 1

record Congruent (a b modulus : Nat) : Set where
  field
    left-multiple : Nat
    right-multiple : Nat
    congruence-equation :
      a + left-multiple * modulus ≡ b + right-multiple * modulus

record QuadraticResidue (a modulus : Nat) : Set where
  field
    root : Nat
    root-square-congruence : Congruent (root * root) a modulus

law-of-quadratic-reciprocity : Set
law-of-quadratic-reciprocity =
  (p q r s : Nat) →
  Prime p →
  Prime q →
  p ≠ q →
  p ≡ 2 * r + 1 →
  q ≡ 2 * s + 1 →
  ((QuadraticResidue q p ↔ QuadraticResidue p q) ↔
   ¬ (Odd r ∧ Odd s))
