-- Statement-only formalization of thousand-theorems corpus artifact Q1057919,
-- "Sylow theorems": existence of prime-power subgroups, conjugacy of Sylow
-- subgroups, divisibility of their index, and their cardinality modulo the
-- prime. This file contains no proof.

module Q1057919_sylow_theorems where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤_ _∣_ _↔_ _⊆_ _≈_
infixr 8 _^_

data ⊥ {ℓ : Level} : Set ℓ where

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬_ {ℓ} A = A → ⊥ {ℓ}

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    forward  : A → B
    backward : B → A

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

_^_ : Nat → Nat → Nat
base ^ zero = suc zero
base ^ suc exponent = base * (base ^ exponent)

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

record SubgroupOf
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G) :
  Set (lsuc ℓ) where

  open Group structure

  field
    member : G → Set ℓ
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

open SubgroupOf

_⊆_ :
  {ℓ : Level} →
  {G : Set ℓ} →
  {structure : Group G} →
  SubgroupOf structure →
  SubgroupOf structure →
  Set ℓ
H ⊆ K =
  (x : _) → member H x → member K x

record _≈_
  {ℓ : Level}
  {G : Set ℓ}
  {structure : Group G}
  (H K : SubgroupOf structure) :
  Set ℓ where

  field
    same-members-forward  : H ⊆ K
    same-members-backward : K ⊆ H

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

IsPGroup :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  Nat →
  SubgroupOf structure →
  Set ℓ
IsPGroup structure prime H =
  (x : _) →
  member H x →
  Σ Nat
    (λ exponent →
      power structure x (prime ^ exponent) ≡
      Group.identity structure)

record IsSylow
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G)
  (prime : Nat)
  (H : SubgroupOf structure) :
  Set (lsuc ℓ) where

  field
    is-p-group : IsPGroup structure prime H
    maximal :
      (K : SubgroupOf structure) →
      IsPGroup structure prime K →
      H ⊆ K →
      K ≈ H

SubgroupCarrier :
  {ℓ : Level} →
  {G : Set ℓ} →
  {structure : Group G} →
  SubgroupOf structure →
  Set ℓ
SubgroupCarrier {G = G} H =
  Σ G (member H)

record SylowEnumeration
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G)
  (prime count : Nat) :
  Set (lsuc ℓ) where

  field
    subgroup-at :
      Fin count →
      SubgroupOf structure
    subgroup-at-is-sylow :
      (i : Fin count) →
      IsSylow structure prime (subgroup-at i)
    complete :
      (H : SubgroupOf structure) →
      IsSylow structure prime H →
      Σ (Fin count)
        (λ i → H ≈ subgroup-at i)
    no-duplicates :
      (i j : Fin count) →
      subgroup-at i ≈ subgroup-at j →
      i ≡ j

ConjugateBy :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  G →
  SubgroupOf structure →
  SubgroupOf structure →
  Set ℓ
ConjugateBy structure g H K =
  let open Group structure
  in
  (x : _) →
  member K x ↔
  member H (multiply (multiply (inverse g) x) g)

SameLeftCoset :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  SubgroupOf structure →
  G →
  G →
  Set ℓ
SameLeftCoset structure H x y =
  let open Group structure
  in
  member H (multiply (inverse x) y)

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

record ModEq (modulus a b : Nat) : Set where
  field
    left-quotient  : Nat
    right-quotient : Nat
    mod-equation :
      a + modulus * left-quotient ≡
      b + modulus * right-quotient

-- Lean: Sylow.exists_subgroup_card_pow_prime
exists-subgroup-card-pow-prime :
  (ℓ : Level) →
  Set (lsuc ℓ)
exists-subgroup-card-pow-prime ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (group-order prime exponent : Nat) →
  Bijection G (Fin group-order) →
  Prime prime →
  prime ^ exponent ∣ group-order →
  Σ (SubgroupOf structure)
    (λ H →
      Bijection
        (SubgroupCarrier H)
        (Fin (prime ^ exponent)))

-- Lean: Sylow.isPretransitive_of_finite
is-pretransitive-of-finite :
  (ℓ : Level) →
  Set (lsuc ℓ)
is-pretransitive-of-finite ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (prime count : Nat) →
  Prime prime →
  SylowEnumeration structure prime count →
  (P Q : SubgroupOf structure) →
  IsSylow structure prime P →
  IsSylow structure prime Q →
  Σ G
    (λ g → ConjugateBy structure g P Q)

-- Lean: Sylow.card_dvd_index
card-sylow-divides-index :
  (ℓ : Level) →
  Set (lsuc ℓ)
card-sylow-divides-index ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (prime sylow-count subgroup-index : Nat) →
  Prime prime →
  SylowEnumeration structure prime sylow-count →
  (P : SubgroupOf structure) →
  IsSylow structure prime P →
  Index structure P subgroup-index →
  sylow-count ∣ subgroup-index

-- Lean: card_sylow_modEq_one
card-sylow-modEq-one :
  (ℓ : Level) →
  Set (lsuc ℓ)
card-sylow-modEq-one ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (prime sylow-count : Nat) →
  Prime prime →
  SylowEnumeration structure prime sylow-count →
  ModEq prime sylow-count (suc zero)
