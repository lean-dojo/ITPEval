-- Statement-only formalization of thousand-theorems corpus artifact Q1139041,
-- "Cauchy's theorem (group theory)": every prime divisor of the order of a
-- finite group is the order of some group element. This file contains no proof.

module Q1139041_cauchy_s_theorem_group_theory where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤_ _∣_

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

data _≤_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    divides-equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : suc (suc zero) ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      (d ≡ suc zero) ∨ (d ≡ n)

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

power :
  {ℓ : Level} →
  {G : Set ℓ} →
  Group G →
  G →
  Nat →
  G
power structure x zero = Group.identity structure
power structure x (suc n) =
  Group.multiply structure x (power structure x n)

record ExactOrder
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G)
  (x : G)
  (n : Nat) :
  Set ℓ where

  field
    power-is-identity :
      power structure x n ≡ Group.identity structure
    least-positive :
      (k : Nat) →
      suc zero ≤ k →
      power structure x k ≡ Group.identity structure →
      n ≤ k

cauchys-theorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
cauchys-theorem ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (group-order prime : Nat) →
  Bijection G (Fin group-order) →
  Prime prime →
  prime ∣ group-order →
  Σ G (λ x → ExactOrder structure x prime)
