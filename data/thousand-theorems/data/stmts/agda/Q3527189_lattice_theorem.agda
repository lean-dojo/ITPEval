-- Statement-only formalization of thousand-theorems corpus artifact Q3527189,
-- "Lattice theorem": Noether's third isomorphism theorem gives the canonical
-- group isomorphism (G / N) / (M / N) ≅ G / M for normal subgroups N contained
-- in M. This file contains no proof.

module Q3527189_lattice_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _⊆_
infixr 5 _×_

data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    first  : A
    second : B

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

_⊆_ :
  {ℓ : Level} →
  {G : Set ℓ} →
  {structure : Group G} →
  SubgroupOf structure →
  SubgroupOf structure →
  Set ℓ
H ⊆ K =
  (x : _) →
  SubgroupOf.member H x →
  SubgroupOf.member K x

record Normal
  {ℓ : Level}
  {G : Set ℓ}
  {structure : Group G}
  (N : SubgroupOf structure) :
  Set ℓ where

  field
    closed-under-conjugation :
      (g n : G) →
      SubgroupOf.member N n →
      SubgroupOf.member N
        (Group.multiply structure
          (Group.multiply structure g n)
          (Group.inverse structure g))

record RestrictedMulEquiv
  {a b p q r s : Level}
  (A : Set a)
  (B : Set b)
  (domain-member : A → Set p)
  (codomain-member : B → Set q)
  (domain-related : A → A → Set r)
  (codomain-related : B → B → Set s)
  (domain-multiply : A → A → A)
  (codomain-multiply : B → B → B)
  (forward : A → B) :
  Set (a ⊔ b ⊔ p ⊔ q ⊔ r ⊔ s) where

  field
    inverse :
      (y : B) →
      codomain-member y →
      A
    forward-closed :
      (x : A) →
      domain-member x →
      codomain-member (forward x)
    inverse-closed :
      (y : B) →
      (hy : codomain-member y) →
      domain-member (inverse y hy)
    forward-congruent :
      (x y : A) →
      domain-member x →
      domain-member y →
      domain-related x y →
      codomain-related (forward x) (forward y)
    inverse-congruent :
      (x y : B) →
      (hx : codomain-member x) →
      (hy : codomain-member y) →
      codomain-related x y →
      domain-related (inverse x hx) (inverse y hy)
    map-multiply :
      (x y : A) →
      domain-member x →
      domain-member y →
      codomain-related
        (forward (domain-multiply x y))
        (codomain-multiply (forward x) (forward y))
    inverse-forward :
      (x : A) →
      (hx : domain-member x) →
      domain-related
        (inverse (forward x) (forward-closed x hx))
        x
    forward-inverse :
      (y : B) →
      (hy : codomain-member y) →
      codomain-related (forward (inverse y hy)) y

QuotientRelated :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  SubgroupOf structure →
  G →
  G →
  Set ℓ
QuotientRelated structure N x y =
  SubgroupOf.member N
    (Group.multiply structure (Group.inverse structure x) y)

DoubleQuotientRelated :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  (N M : SubgroupOf structure) →
  G →
  G →
  Set ℓ
DoubleQuotientRelated {G = G} structure N M x y =
  Σ G (λ m →
    SubgroupOf.member M m ×
    QuotientRelated structure N m
      (Group.multiply structure (Group.inverse structure x) y))

-- Lean: QuotientGroup.quotientQuotientEquivQuotient
lattice-theorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
lattice-theorem ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (N M : SubgroupOf structure) →
  Normal N →
  Normal M →
  N ⊆ M →
  RestrictedMulEquiv
    G
    G
    (λ _ → ⊤ {ℓ})
    (λ _ → ⊤ {ℓ})
    (DoubleQuotientRelated structure N M)
    (QuotientRelated structure M)
    (Group.multiply structure)
    (Group.multiply structure)
    (λ x → x)
