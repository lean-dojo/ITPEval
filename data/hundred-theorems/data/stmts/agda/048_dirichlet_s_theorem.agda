-- Statement-only formalization of "Dirichlet's Theorem" from Hundred Theorems item 048:
-- every coprime residue class modulo a positive natural number contains a prime above every
-- natural bound. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _≤_ _<_ _∣_
infixr 5 _×_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _×_ (A B : Set) : Set where
  constructor pair
  field
    left : A
    right : B

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat → Nat → Nat → Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat → Nat → Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

Coprime : Nat → Nat → Set
Coprime a b = naturalGCD a b ≡ 1

ModEq : Nat → Nat → Nat → Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus ≡ naturalMod rhs modulus

dirichlet-s-theorem : Set
dirichlet-s-theorem =
  (d k : Nat) →
  1 ≤ d →
  Coprime k d →
  (bound : Nat) →
  Exists Nat
    (λ p →
      Prime p ×
      ((bound < p) × ModEq d p k))
