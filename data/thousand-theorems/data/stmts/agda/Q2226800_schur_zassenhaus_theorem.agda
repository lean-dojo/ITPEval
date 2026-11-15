-- Statement-only formalization of thousand-theorems corpus artifact Q2226800,
-- "Schur-Zassenhaus theorem": a normal subgroup whose order is coprime to its
-- index has a subgroup forming a left multiplicative complement. This file
-- contains no proof.

module Q2226800_schur_zassenhaus_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _∣_
infixr 5 _×_

data ⊥ {ℓ : Level} : Set ℓ where

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    divides-equation : divisor * quotient ≡ dividend

Coprime : Nat → Nat → Set
Coprime m n =
  (d : Nat) →
  d ∣ m →
  d ∣ n →
  d ≡ suc zero

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

record Normal
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G)
  (N : SubgroupOf structure) :
  Set ℓ where

  field
    closed-under-conjugation :
      (g n : G) →
      member N n →
      member N
        (Group.multiply structure
          (Group.multiply structure g n)
          (Group.inverse structure g))

SameLeftCoset :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  SubgroupOf structure →
  G →
  G →
  Set ℓ
SameLeftCoset structure H x y =
  member H
    (Group.multiply structure
      (Group.inverse structure x)
      y)

record CosetTransversal
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G)
  (H : SubgroupOf structure)
  (count : Nat) :
  Set ℓ where

  field
    representative :
      Fin count →
      G
    covers :
      (x : G) →
      Σ (Fin count)
        (λ i →
          SameLeftCoset structure H (representative i) x)
    unique :
      (i j : Fin count) →
      SameLeftCoset
        structure H (representative i) (representative j) →
      i ≡ j

InfiniteIndex :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  SubgroupOf structure →
  Set ℓ
InfiniteIndex {ℓ = ℓ} structure H =
  (count : Nat) →
  CosetTransversal structure H count →
  ⊥ {ℓ}

data Index
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G)
  (H : SubgroupOf structure) :
  Nat →
  Set ℓ where

  finite-index :
    {count : Nat} →
    CosetTransversal structure H count →
    Index structure H count

  infinite-index :
    {count : Nat} →
    count ≡ zero →
    InfiniteIndex structure H →
    Index structure H count

record IsComplement'
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G)
  (H K : SubgroupOf structure) :
  Set (lsuc ℓ) where

  field
    factorization :
      (g : G) →
      Σ G
        (λ h →
          member H h ×
          Σ G
            (λ k →
              member K k ×
              (Group.multiply structure h k ≡ g)))
    factorization-unique :
      (h₁ k₁ h₂ k₂ : G) →
      member H h₁ →
      member K k₁ →
      member H h₂ →
      member K k₂ →
      Group.multiply structure h₁ k₁ ≡
        Group.multiply structure h₂ k₂ →
      (h₁ ≡ h₂) × (k₁ ≡ k₂)

-- Lean: Subgroup.exists_left_complement'_of_coprime
schur-zassenhaus-theorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
schur-zassenhaus-theorem ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (N : SubgroupOf structure) →
  Normal structure N →
  (subgroup-order subgroup-index : Nat) →
  NatCard (SubgroupCarrier N) subgroup-order →
  Index structure N subgroup-index →
  Coprime subgroup-order subgroup-index →
  Σ (SubgroupOf structure)
    (λ H → IsComplement' structure H N)
