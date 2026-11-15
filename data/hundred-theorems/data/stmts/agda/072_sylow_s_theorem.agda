-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__072, "Sylow's Theorem": a finite group whose
-- order is divisible by a prime power has a subgroup of that order.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _≤_ _∣_
infixr 8 _^_

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

data _≤_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      (d ≡ 1) ∨ (d ≡ n)

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

record Group {ℓ : Level} (G : Set ℓ) : Set ℓ where
  field
    identity       : G
    inverse        : G → G
    multiply       : G → G → G
    associative    : (x y z : G) →
                     multiply x (multiply y z) ≡
                     multiply (multiply x y) z
    identity-left  : (x : G) → multiply identity x ≡ x
    identity-right : (x : G) → multiply x identity ≡ x
    inverse-left   : (x : G) → multiply (inverse x) x ≡ identity
    inverse-right  : (x : G) → multiply x (inverse x) ≡ identity

record Subgroup
  {ℓ p : Level}
  {G : Set ℓ}
  (structure : Group G)
  (member : G → Set p) :
  Set (ℓ ⊔ p) where

  open Group structure

  field
    membership-propositional :
      (x : G) (u v : member x) → u ≡ v
    contains-identity : member identity
    closed-under-inverse :
      (x : G) → member x → member (inverse x)
    closed-under-multiply :
      (x y : G) →
      member x →
      member y →
      member (multiply x y)

sylows-theorem :
  (ℓ p : Level) →
  Set (lsuc (ℓ ⊔ p))
sylows-theorem ℓ p =
  {G : Set ℓ} →
  (structure : Group G) →
  (group-order prime exponent : Nat) →
  Bijection G (Fin group-order) →
  Prime prime →
  prime ^ exponent ∣ group-order →
  Σ (G → Set p) (λ member →
    Σ (Subgroup structure member) (λ _ →
      Bijection
        (Σ G member)
        (Fin (prime ^ exponent))))
