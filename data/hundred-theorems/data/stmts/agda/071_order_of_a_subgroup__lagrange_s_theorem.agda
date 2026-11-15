-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__071, "Order of a Subgroup (Lagrange's Theorem)":
-- the order of a subgroup of a finite group divides the order of the group.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _∣_

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

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

record Group {ℓ : Level} (G : Set ℓ) : Set ℓ where
  field
    identity      : G
    inverse       : G → G
    multiply      : G → G → G
    associative   : (x y z : G) →
                    multiply x (multiply y z) ≡
                    multiply (multiply x y) z
    identity-left : (x : G) → multiply identity x ≡ x
    identity-right : (x : G) → multiply x identity ≡ x
    inverse-left  : (x : G) → multiply (inverse x) x ≡ identity
    inverse-right : (x : G) → multiply x (inverse x) ≡ identity

record Subgroup
  {ℓ p : Level}
  {G : Set ℓ}
  (S : Group G)
  (member : G → Set p) :
  Set (ℓ ⊔ p) where

  open Group S

  field
    membership-propositional :
      (x : G) (u v : member x) → u ≡ v
    contains-identity : member identity
    closed-under-inverse :
      (x : G) → member x → member (inverse x)
    closed-under-multiply :
      (x y : G) → member x → member y → member (multiply x y)

lagranges-theorem :
  (ℓ p : Level) →
  Set (lsuc (ℓ ⊔ p))
lagranges-theorem ℓ p =
  {G : Set ℓ} →
  (S : Group G) →
  (member : G → Set p) →
  Subgroup S member →
  (group-order subgroup-order : Nat) →
  Bijection G (Fin group-order) →
  Bijection (Σ G member) (Fin subgroup-order) →
  subgroup-order ∣ group-order
