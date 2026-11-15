-- Statement-only formalization of thousand-theorems corpus artifact Q505798,
-- "Lagrange's theorem (group theory)": the natural cardinality of a subgroup
-- divides the natural cardinality of its ambient group. This file contains no
-- proof.

module Q505798_lagrange_s_theorem_group_theory where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _∣_

data ⊥ {ℓ : Level} : Set ℓ where

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (Agda.Builtin.Nat.suc n)
  fsuc  : {n : Nat} → Fin n → Fin (Agda.Builtin.Nat.suc n)

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

InfiniteCard :
  {ℓ : Level} →
  Set ℓ →
  Set ℓ
InfiniteCard {ℓ} A =
  (count : Nat) →
  Bijection A (Fin count) →
  ⊥ {ℓ}

data NatCard
  {ℓ : Level}
  (A : Set ℓ) :
  Nat →
  Set ℓ where

  finite-card :
    {count : Nat} →
    Bijection A (Fin count) →
    NatCard A count

  infinite-card :
    {count : Nat} →
    count ≡ zero →
    InfiniteCard A →
    NatCard A count

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    divides-equation : divisor * quotient ≡ dividend

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

record SubgroupOf
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G) :
  Set (lsuc ℓ) where

  field
    member : G → Set ℓ
    membership-propositional :
      (x : G) (u v : member x) → u ≡ v
    contains-identity :
      member (Group.identity structure)
    closed-under-inverse :
      (x : G) →
      member x →
      member (Group.inverse structure x)
    closed-under-multiply :
      (x y : G) →
      member x →
      member y →
      member (Group.multiply structure x y)

open SubgroupOf

SubgroupCarrier :
  {ℓ : Level} →
  {G : Set ℓ} →
  {structure : Group G} →
  SubgroupOf structure →
  Set ℓ
SubgroupCarrier {G = G} H =
  Σ G (member H)

-- Lean: Subgroup.card_subgroup_dvd_card
lagranges-theorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
lagranges-theorem ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (H : SubgroupOf structure) →
  (subgroup-order group-order : Nat) →
  NatCard (SubgroupCarrier H) subgroup-order →
  NatCard G group-order →
  subgroup-order ∣ group-order
